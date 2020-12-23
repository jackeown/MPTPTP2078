%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:45 EST 2020

% Result     : Theorem 15.10s
% Output     : CNFRefutation 15.10s
% Verified   : 
% Statistics : Number of formulae       :  238 (40771 expanded)
%              Number of clauses        :  197 (17969 expanded)
%              Number of leaves         :   15 (10516 expanded)
%              Depth                    :   39
%              Number of atoms          :  277 (45228 expanded)
%              Number of equality atoms :  229 (39043 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :   14 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f40,f36,f36])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f44,f36])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_tarski(sK1,sK2) )
      & r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( ~ r1_xboole_0(sK1,sK3)
      | ~ r1_tarski(sK1,sK2) )
    & r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f25])).

fof(f45,plain,(
    r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(definition_unfolding,[],[f45,f36])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1029,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_849,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_1])).

cnf(c_10,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_938,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_849,c_10])).

cnf(c_1573,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_938])).

cnf(c_21904,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1029,c_1573])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_681,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_814,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_681])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_683,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1496,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_814,c_683])).

cnf(c_1728,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1496,c_12])).

cnf(c_14,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_705,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_14,c_1])).

cnf(c_4913,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_705,c_10])).

cnf(c_12810,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) = k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)) ),
    inference(superposition,[status(thm)],[c_1728,c_4913])).

cnf(c_703,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_14,c_1])).

cnf(c_15,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_950,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_15,c_14])).

cnf(c_957,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_950,c_849])).

cnf(c_1097,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_957])).

cnf(c_1197,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1097,c_1097])).

cnf(c_1398,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_1197,c_14])).

cnf(c_9031,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
    inference(superposition,[status(thm)],[c_703,c_1398])).

cnf(c_1193,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
    inference(superposition,[status(thm)],[c_957,c_1097])).

cnf(c_1302,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_1193,c_14])).

cnf(c_8706,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_1302,c_1302])).

cnf(c_9145,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_9031,c_8706])).

cnf(c_704,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_14,c_1])).

cnf(c_3713,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_1197,c_704])).

cnf(c_3736,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
    inference(light_normalisation,[status(thm)],[c_3713,c_14])).

cnf(c_10946,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,X3),X2) ),
    inference(superposition,[status(thm)],[c_703,c_3736])).

cnf(c_11040,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X1,k5_xboole_0(X3,X2)) ),
    inference(demodulation,[status(thm)],[c_10946,c_3736,c_9145])).

cnf(c_13060,plain,
    ( k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) ),
    inference(demodulation,[status(thm)],[c_12810,c_9145,c_11040])).

cnf(c_939,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_1819,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_14,c_1728])).

cnf(c_2011,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_1819,c_12])).

cnf(c_9,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_684,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1827,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1728,c_684])).

cnf(c_1995,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1827,c_683])).

cnf(c_3084,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),X1)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
    inference(superposition,[status(thm)],[c_1995,c_12])).

cnf(c_9434,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
    inference(light_normalisation,[status(thm)],[c_2011,c_2011,c_3084])).

cnf(c_9435,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
    inference(demodulation,[status(thm)],[c_9434,c_2011,c_9145])).

cnf(c_9436,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
    inference(demodulation,[status(thm)],[c_9435,c_9145])).

cnf(c_9449,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1)))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))) ),
    inference(superposition,[status(thm)],[c_939,c_9436])).

cnf(c_8699,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
    inference(superposition,[status(thm)],[c_1302,c_14])).

cnf(c_3709,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_13,c_704])).

cnf(c_4923,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_705,c_3709])).

cnf(c_4687,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_3709,c_703])).

cnf(c_4939,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_4923,c_4687])).

cnf(c_8745,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
    inference(demodulation,[status(thm)],[c_8699,c_4939])).

cnf(c_9538,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) ),
    inference(demodulation,[status(thm)],[c_9449,c_8745,c_9145])).

cnf(c_3727,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_704,c_957])).

cnf(c_9539,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1)))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_9538,c_3727,c_9145])).

cnf(c_1105,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_957,c_10])).

cnf(c_1824,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)))) ),
    inference(superposition,[status(thm)],[c_1105,c_1728])).

cnf(c_1043,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_684])).

cnf(c_1498,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1043,c_683])).

cnf(c_1835,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1824,c_15,c_1398,c_1496,c_1498])).

cnf(c_1836,plain,
    ( k3_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1835,c_15])).

cnf(c_9540,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1)))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9539,c_15,c_1836])).

cnf(c_15723,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)))),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13060,c_9540])).

cnf(c_1190,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_14,c_1097])).

cnf(c_7434,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0)))) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_1190,c_703])).

cnf(c_15728,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15723,c_3727,c_7434,c_11040])).

cnf(c_5926,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))) = sK1 ),
    inference(superposition,[status(thm)],[c_1819,c_939])).

cnf(c_4926,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
    inference(superposition,[status(thm)],[c_705,c_957])).

cnf(c_6045,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) = sK1 ),
    inference(demodulation,[status(thm)],[c_5926,c_4926])).

cnf(c_15729,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15728,c_15,c_6045,c_9145])).

cnf(c_17483,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_15729])).

cnf(c_17579,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17483,c_0])).

cnf(c_1026,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_19041,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_17579,c_1026])).

cnf(c_953,plain,
    ( k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1)))))) = k5_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_14,c_10])).

cnf(c_937,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_849,c_10])).

cnf(c_1475,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12,c_937])).

cnf(c_9149,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1475])).

cnf(c_15364,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_9149])).

cnf(c_9154,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1573,c_1475])).

cnf(c_15398,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15364,c_13,c_9154])).

cnf(c_17174,plain,
    ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_953,c_15398])).

cnf(c_19119,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19041,c_849,c_17174])).

cnf(c_21916,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_21904,c_13,c_19119])).

cnf(c_1099,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_12,c_957])).

cnf(c_33807,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_21916,c_1099])).

cnf(c_29495,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_21916,c_0])).

cnf(c_34148,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)))) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(light_normalisation,[status(thm)],[c_33807,c_29495])).

cnf(c_19051,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1026,c_957])).

cnf(c_29475,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)) ),
    inference(superposition,[status(thm)],[c_21916,c_1029])).

cnf(c_29528,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_29475,c_1029])).

cnf(c_34149,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_34148,c_1029,c_19051,c_29528])).

cnf(c_21810,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1105,c_1029])).

cnf(c_941,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_10,c_10])).

cnf(c_943,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k1_xboole_0)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_941,c_15])).

cnf(c_944,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_943,c_13])).

cnf(c_19056,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))))),k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1026,c_944])).

cnf(c_19072,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X3,k3_xboole_0(X0,X1)))) = k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3)))) ),
    inference(superposition,[status(thm)],[c_1026,c_703])).

cnf(c_19112,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))))),k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))))) ),
    inference(demodulation,[status(thm)],[c_19056,c_19072])).

cnf(c_1276,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1105,c_10])).

cnf(c_1279,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1276,c_15])).

cnf(c_1280,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_1279,c_13])).

cnf(c_19113,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_19112,c_1099,c_1280,c_1498])).

cnf(c_22000,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21810,c_15,c_19113])).

cnf(c_29937,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_22000,c_1819])).

cnf(c_29938,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_22000,c_1728])).

cnf(c_1032,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
    inference(superposition,[status(thm)],[c_12,c_14])).

cnf(c_26358,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X1))),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_1105,c_1032])).

cnf(c_19007,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1573,c_1026])).

cnf(c_19205,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_19007,c_19119])).

cnf(c_19206,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_19205,c_13])).

cnf(c_26597,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(light_normalisation,[status(thm)],[c_26358,c_1498,c_19206])).

cnf(c_29950,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,sK3),k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_29938,c_26597])).

cnf(c_29951,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_29950,c_13])).

cnf(c_29952,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k1_xboole_0))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_29937,c_29951])).

cnf(c_29953,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) = sK1 ),
    inference(demodulation,[status(thm)],[c_29952,c_13,c_1496])).

cnf(c_33823,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),sK1) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_29953,c_1099])).

cnf(c_34150,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),sK1) = k3_xboole_0(sK3,k3_xboole_0(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_34149,c_33823])).

cnf(c_19006,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_1496,c_1026])).

cnf(c_19207,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_19006,c_1728,c_1819,c_9145])).

cnf(c_20159,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(sK1,X1) ),
    inference(superposition,[status(thm)],[c_19207,c_1302])).

cnf(c_45817,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK3,k3_xboole_0(sK2,sK1))) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_34150,c_20159])).

cnf(c_20165,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),X1) = k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),X1)) ),
    inference(superposition,[status(thm)],[c_19207,c_14])).

cnf(c_15724,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) ),
    inference(superposition,[status(thm)],[c_13060,c_9436])).

cnf(c_15725,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) ),
    inference(demodulation,[status(thm)],[c_15724,c_8745])).

cnf(c_15726,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_15725,c_3727])).

cnf(c_15727,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15726,c_15,c_1836])).

cnf(c_1188,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_12,c_1097])).

cnf(c_37550,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))),k1_xboole_0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) ),
    inference(superposition,[status(thm)],[c_15727,c_1188])).

cnf(c_33837,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_15727,c_1099])).

cnf(c_33843,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22000,c_1099])).

cnf(c_34095,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_33843,c_29495])).

cnf(c_34103,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ),
    inference(demodulation,[status(thm)],[c_33837,c_34095])).

cnf(c_20125,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(X0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_19207,c_1193])).

cnf(c_20896,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1105,c_20125])).

cnf(c_1495,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_684,c_683])).

cnf(c_20997,plain,
    ( k3_xboole_0(sK1,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_20896,c_15,c_849,c_1495,c_9145])).

cnf(c_22079,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_20997,c_1026])).

cnf(c_34104,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_34103,c_1995,c_22079])).

cnf(c_37845,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k1_xboole_0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_37550,c_1995,c_34104])).

cnf(c_1033,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0))))) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_10])).

cnf(c_33826,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_1033,c_1099])).

cnf(c_34123,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_33826,c_15,c_1498])).

cnf(c_34562,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_34123])).

cnf(c_1820,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_1728])).

cnf(c_38438,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_34562,c_1820])).

cnf(c_38445,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,sK3),k1_xboole_0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(demodulation,[status(thm)],[c_38438,c_26597])).

cnf(c_38446,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = sK1 ),
    inference(demodulation,[status(thm)],[c_38445,c_1496,c_34095])).

cnf(c_2627,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_703,c_10])).

cnf(c_10495,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k3_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))) ),
    inference(superposition,[status(thm)],[c_2627,c_9436])).

cnf(c_10496,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k3_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) ),
    inference(demodulation,[status(thm)],[c_10495,c_8745,c_9145])).

cnf(c_10497,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k3_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_10496,c_3727,c_9145])).

cnf(c_10498,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k3_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10497,c_15,c_1836])).

cnf(c_11719,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1819,c_10498])).

cnf(c_39765,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),sK3),sK1))))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_38446,c_11719])).

cnf(c_20126,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k3_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_19207,c_957])).

cnf(c_9451,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k1_xboole_0))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))) ),
    inference(superposition,[status(thm)],[c_1573,c_9436])).

cnf(c_9531,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k1_xboole_0)))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) ),
    inference(demodulation,[status(thm)],[c_9451,c_8745,c_9145])).

cnf(c_9532,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
    inference(demodulation,[status(thm)],[c_9531,c_3727,c_9145,c_9436])).

cnf(c_9533,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k1_xboole_0)))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_9532,c_1836])).

cnf(c_9534,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(sK1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9533,c_13,c_15,c_957,c_1836,c_1995])).

cnf(c_9705,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_9534])).

cnf(c_20148,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19207,c_9705])).

cnf(c_21356,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20148,c_0])).

cnf(c_33842,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),sK1),X0) = k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_21356,c_1099])).

cnf(c_34096,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),sK1),X0) = k3_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(demodulation,[status(thm)],[c_33842,c_34095])).

cnf(c_1041,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_684])).

cnf(c_1497,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1041,c_683])).

cnf(c_21358,plain,
    ( k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))) = k5_xboole_0(k3_xboole_0(X0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_20148,c_1026])).

cnf(c_3088,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1995,c_0])).

cnf(c_21360,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,sK1)) = k5_xboole_0(k3_xboole_0(X0,sK1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_21358,c_3088,c_20126])).

cnf(c_21361,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,sK1)) = k3_xboole_0(X0,sK1) ),
    inference(demodulation,[status(thm)],[c_21360,c_13])).

cnf(c_22536,plain,
    ( k3_xboole_0(X0,k3_xboole_0(sK1,X0)) = k3_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_21361])).

cnf(c_23769,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X0,sK1)))) = k3_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_22536,c_2627])).

cnf(c_21076,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_20126,c_1190])).

cnf(c_21084,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21076,c_15])).

cnf(c_23955,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,X0),X0) = k3_xboole_0(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_23769,c_13,c_21084])).

cnf(c_24439,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK1),X0) = k3_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_23955])).

cnf(c_34097,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_34096,c_1497,c_24439])).

cnf(c_39818,plain,
    ( k3_xboole_0(sK1,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_39765,c_1819,c_7434,c_20126,c_22079,c_34097])).

cnf(c_40053,plain,
    ( k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,k5_xboole_0(sK1,k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,sK1),sK3) ),
    inference(superposition,[status(thm)],[c_39818,c_1099])).

cnf(c_40225,plain,
    ( k3_xboole_0(k3_xboole_0(X0,sK1),sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_40053,c_13,c_15])).

cnf(c_42448,plain,
    ( k3_xboole_0(sK3,k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_40225,c_0])).

cnf(c_46032,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45817,c_15,c_20165,c_37845,c_42448])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_709,plain,
    ( r1_tarski(sK1,sK2)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_103,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_343,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k3_xboole_0(X0,X1) != k1_xboole_0
    | sK3 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_103,c_16])).

cnf(c_344,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k3_xboole_0(sK1,sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46032,c_39818,c_709,c_344])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:14:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 15.10/2.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.10/2.51  
% 15.10/2.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.10/2.51  
% 15.10/2.51  ------  iProver source info
% 15.10/2.51  
% 15.10/2.51  git: date: 2020-06-30 10:37:57 +0100
% 15.10/2.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.10/2.51  git: non_committed_changes: false
% 15.10/2.51  git: last_make_outside_of_git: false
% 15.10/2.51  
% 15.10/2.51  ------ 
% 15.10/2.51  
% 15.10/2.51  ------ Input Options
% 15.10/2.51  
% 15.10/2.51  --out_options                           all
% 15.10/2.51  --tptp_safe_out                         true
% 15.10/2.51  --problem_path                          ""
% 15.10/2.51  --include_path                          ""
% 15.10/2.51  --clausifier                            res/vclausify_rel
% 15.10/2.51  --clausifier_options                    ""
% 15.10/2.51  --stdin                                 false
% 15.10/2.51  --stats_out                             all
% 15.10/2.51  
% 15.10/2.51  ------ General Options
% 15.10/2.51  
% 15.10/2.51  --fof                                   false
% 15.10/2.51  --time_out_real                         305.
% 15.10/2.51  --time_out_virtual                      -1.
% 15.10/2.51  --symbol_type_check                     false
% 15.10/2.51  --clausify_out                          false
% 15.10/2.51  --sig_cnt_out                           false
% 15.10/2.51  --trig_cnt_out                          false
% 15.10/2.51  --trig_cnt_out_tolerance                1.
% 15.10/2.51  --trig_cnt_out_sk_spl                   false
% 15.10/2.51  --abstr_cl_out                          false
% 15.10/2.51  
% 15.10/2.51  ------ Global Options
% 15.10/2.51  
% 15.10/2.51  --schedule                              default
% 15.10/2.51  --add_important_lit                     false
% 15.10/2.51  --prop_solver_per_cl                    1000
% 15.10/2.51  --min_unsat_core                        false
% 15.10/2.51  --soft_assumptions                      false
% 15.10/2.51  --soft_lemma_size                       3
% 15.10/2.51  --prop_impl_unit_size                   0
% 15.10/2.51  --prop_impl_unit                        []
% 15.10/2.51  --share_sel_clauses                     true
% 15.10/2.51  --reset_solvers                         false
% 15.10/2.51  --bc_imp_inh                            [conj_cone]
% 15.10/2.51  --conj_cone_tolerance                   3.
% 15.10/2.51  --extra_neg_conj                        none
% 15.10/2.51  --large_theory_mode                     true
% 15.10/2.51  --prolific_symb_bound                   200
% 15.10/2.51  --lt_threshold                          2000
% 15.10/2.51  --clause_weak_htbl                      true
% 15.10/2.51  --gc_record_bc_elim                     false
% 15.10/2.51  
% 15.10/2.51  ------ Preprocessing Options
% 15.10/2.51  
% 15.10/2.51  --preprocessing_flag                    true
% 15.10/2.51  --time_out_prep_mult                    0.1
% 15.10/2.51  --splitting_mode                        input
% 15.10/2.51  --splitting_grd                         true
% 15.10/2.51  --splitting_cvd                         false
% 15.10/2.51  --splitting_cvd_svl                     false
% 15.10/2.51  --splitting_nvd                         32
% 15.10/2.51  --sub_typing                            true
% 15.10/2.51  --prep_gs_sim                           true
% 15.10/2.51  --prep_unflatten                        true
% 15.10/2.51  --prep_res_sim                          true
% 15.10/2.51  --prep_upred                            true
% 15.10/2.51  --prep_sem_filter                       exhaustive
% 15.10/2.51  --prep_sem_filter_out                   false
% 15.10/2.51  --pred_elim                             true
% 15.10/2.51  --res_sim_input                         true
% 15.10/2.51  --eq_ax_congr_red                       true
% 15.10/2.51  --pure_diseq_elim                       true
% 15.10/2.51  --brand_transform                       false
% 15.10/2.51  --non_eq_to_eq                          false
% 15.10/2.51  --prep_def_merge                        true
% 15.10/2.51  --prep_def_merge_prop_impl              false
% 15.10/2.51  --prep_def_merge_mbd                    true
% 15.10/2.51  --prep_def_merge_tr_red                 false
% 15.10/2.51  --prep_def_merge_tr_cl                  false
% 15.10/2.51  --smt_preprocessing                     true
% 15.10/2.51  --smt_ac_axioms                         fast
% 15.10/2.51  --preprocessed_out                      false
% 15.10/2.51  --preprocessed_stats                    false
% 15.10/2.51  
% 15.10/2.51  ------ Abstraction refinement Options
% 15.10/2.51  
% 15.10/2.51  --abstr_ref                             []
% 15.10/2.51  --abstr_ref_prep                        false
% 15.10/2.51  --abstr_ref_until_sat                   false
% 15.10/2.51  --abstr_ref_sig_restrict                funpre
% 15.10/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.10/2.51  --abstr_ref_under                       []
% 15.10/2.51  
% 15.10/2.51  ------ SAT Options
% 15.10/2.51  
% 15.10/2.51  --sat_mode                              false
% 15.10/2.51  --sat_fm_restart_options                ""
% 15.10/2.51  --sat_gr_def                            false
% 15.10/2.51  --sat_epr_types                         true
% 15.10/2.51  --sat_non_cyclic_types                  false
% 15.10/2.51  --sat_finite_models                     false
% 15.10/2.51  --sat_fm_lemmas                         false
% 15.10/2.51  --sat_fm_prep                           false
% 15.10/2.51  --sat_fm_uc_incr                        true
% 15.10/2.51  --sat_out_model                         small
% 15.10/2.51  --sat_out_clauses                       false
% 15.10/2.51  
% 15.10/2.51  ------ QBF Options
% 15.10/2.51  
% 15.10/2.51  --qbf_mode                              false
% 15.10/2.51  --qbf_elim_univ                         false
% 15.10/2.51  --qbf_dom_inst                          none
% 15.10/2.51  --qbf_dom_pre_inst                      false
% 15.10/2.51  --qbf_sk_in                             false
% 15.10/2.51  --qbf_pred_elim                         true
% 15.10/2.51  --qbf_split                             512
% 15.10/2.51  
% 15.10/2.51  ------ BMC1 Options
% 15.10/2.51  
% 15.10/2.51  --bmc1_incremental                      false
% 15.10/2.51  --bmc1_axioms                           reachable_all
% 15.10/2.51  --bmc1_min_bound                        0
% 15.10/2.51  --bmc1_max_bound                        -1
% 15.10/2.51  --bmc1_max_bound_default                -1
% 15.10/2.51  --bmc1_symbol_reachability              true
% 15.10/2.51  --bmc1_property_lemmas                  false
% 15.10/2.51  --bmc1_k_induction                      false
% 15.10/2.51  --bmc1_non_equiv_states                 false
% 15.10/2.51  --bmc1_deadlock                         false
% 15.10/2.51  --bmc1_ucm                              false
% 15.10/2.51  --bmc1_add_unsat_core                   none
% 15.10/2.51  --bmc1_unsat_core_children              false
% 15.10/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.10/2.51  --bmc1_out_stat                         full
% 15.10/2.51  --bmc1_ground_init                      false
% 15.10/2.51  --bmc1_pre_inst_next_state              false
% 15.10/2.51  --bmc1_pre_inst_state                   false
% 15.10/2.51  --bmc1_pre_inst_reach_state             false
% 15.10/2.51  --bmc1_out_unsat_core                   false
% 15.10/2.51  --bmc1_aig_witness_out                  false
% 15.10/2.51  --bmc1_verbose                          false
% 15.10/2.51  --bmc1_dump_clauses_tptp                false
% 15.10/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.10/2.51  --bmc1_dump_file                        -
% 15.10/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.10/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.10/2.51  --bmc1_ucm_extend_mode                  1
% 15.10/2.51  --bmc1_ucm_init_mode                    2
% 15.10/2.51  --bmc1_ucm_cone_mode                    none
% 15.10/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.10/2.51  --bmc1_ucm_relax_model                  4
% 15.10/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.10/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.10/2.51  --bmc1_ucm_layered_model                none
% 15.10/2.51  --bmc1_ucm_max_lemma_size               10
% 15.10/2.51  
% 15.10/2.51  ------ AIG Options
% 15.10/2.51  
% 15.10/2.51  --aig_mode                              false
% 15.10/2.51  
% 15.10/2.51  ------ Instantiation Options
% 15.10/2.51  
% 15.10/2.51  --instantiation_flag                    true
% 15.10/2.51  --inst_sos_flag                         true
% 15.10/2.51  --inst_sos_phase                        true
% 15.10/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.10/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.10/2.51  --inst_lit_sel_side                     num_symb
% 15.10/2.51  --inst_solver_per_active                1400
% 15.10/2.51  --inst_solver_calls_frac                1.
% 15.10/2.51  --inst_passive_queue_type               priority_queues
% 15.10/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.10/2.51  --inst_passive_queues_freq              [25;2]
% 15.10/2.51  --inst_dismatching                      true
% 15.10/2.51  --inst_eager_unprocessed_to_passive     true
% 15.10/2.51  --inst_prop_sim_given                   true
% 15.10/2.51  --inst_prop_sim_new                     false
% 15.10/2.51  --inst_subs_new                         false
% 15.10/2.51  --inst_eq_res_simp                      false
% 15.10/2.51  --inst_subs_given                       false
% 15.10/2.51  --inst_orphan_elimination               true
% 15.10/2.51  --inst_learning_loop_flag               true
% 15.10/2.51  --inst_learning_start                   3000
% 15.10/2.51  --inst_learning_factor                  2
% 15.10/2.51  --inst_start_prop_sim_after_learn       3
% 15.10/2.51  --inst_sel_renew                        solver
% 15.10/2.51  --inst_lit_activity_flag                true
% 15.10/2.51  --inst_restr_to_given                   false
% 15.10/2.51  --inst_activity_threshold               500
% 15.10/2.51  --inst_out_proof                        true
% 15.10/2.51  
% 15.10/2.51  ------ Resolution Options
% 15.10/2.51  
% 15.10/2.51  --resolution_flag                       true
% 15.10/2.51  --res_lit_sel                           adaptive
% 15.10/2.51  --res_lit_sel_side                      none
% 15.10/2.51  --res_ordering                          kbo
% 15.10/2.51  --res_to_prop_solver                    active
% 15.10/2.51  --res_prop_simpl_new                    false
% 15.10/2.51  --res_prop_simpl_given                  true
% 15.10/2.51  --res_passive_queue_type                priority_queues
% 15.10/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.10/2.51  --res_passive_queues_freq               [15;5]
% 15.10/2.51  --res_forward_subs                      full
% 15.10/2.51  --res_backward_subs                     full
% 15.10/2.51  --res_forward_subs_resolution           true
% 15.10/2.51  --res_backward_subs_resolution          true
% 15.10/2.51  --res_orphan_elimination                true
% 15.10/2.51  --res_time_limit                        2.
% 15.10/2.51  --res_out_proof                         true
% 15.10/2.51  
% 15.10/2.51  ------ Superposition Options
% 15.10/2.51  
% 15.10/2.51  --superposition_flag                    true
% 15.10/2.51  --sup_passive_queue_type                priority_queues
% 15.10/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.10/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.10/2.51  --demod_completeness_check              fast
% 15.10/2.51  --demod_use_ground                      true
% 15.10/2.51  --sup_to_prop_solver                    passive
% 15.10/2.51  --sup_prop_simpl_new                    true
% 15.10/2.51  --sup_prop_simpl_given                  true
% 15.10/2.51  --sup_fun_splitting                     true
% 15.10/2.51  --sup_smt_interval                      50000
% 15.10/2.51  
% 15.10/2.51  ------ Superposition Simplification Setup
% 15.10/2.51  
% 15.10/2.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.10/2.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.10/2.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.10/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.10/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.10/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.10/2.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.10/2.51  --sup_immed_triv                        [TrivRules]
% 15.10/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.10/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.10/2.51  --sup_immed_bw_main                     []
% 15.10/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.10/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.10/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.10/2.51  --sup_input_bw                          []
% 15.10/2.51  
% 15.10/2.51  ------ Combination Options
% 15.10/2.51  
% 15.10/2.51  --comb_res_mult                         3
% 15.10/2.51  --comb_sup_mult                         2
% 15.10/2.51  --comb_inst_mult                        10
% 15.10/2.51  
% 15.10/2.51  ------ Debug Options
% 15.10/2.51  
% 15.10/2.51  --dbg_backtrace                         false
% 15.10/2.51  --dbg_dump_prop_clauses                 false
% 15.10/2.51  --dbg_dump_prop_clauses_file            -
% 15.10/2.51  --dbg_out_stat                          false
% 15.10/2.51  ------ Parsing...
% 15.10/2.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.10/2.51  
% 15.10/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.10/2.51  
% 15.10/2.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.10/2.51  
% 15.10/2.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.10/2.51  ------ Proving...
% 15.10/2.51  ------ Problem Properties 
% 15.10/2.51  
% 15.10/2.51  
% 15.10/2.51  clauses                                 18
% 15.10/2.51  conjectures                             2
% 15.10/2.51  EPR                                     2
% 15.10/2.51  Horn                                    16
% 15.10/2.51  unary                                   9
% 15.10/2.51  binary                                  8
% 15.10/2.51  lits                                    28
% 15.10/2.51  lits eq                                 12
% 15.10/2.51  fd_pure                                 0
% 15.10/2.51  fd_pseudo                               0
% 15.10/2.51  fd_cond                                 0
% 15.10/2.51  fd_pseudo_cond                          0
% 15.10/2.51  AC symbols                              1
% 15.10/2.51  
% 15.10/2.51  ------ Schedule dynamic 5 is on 
% 15.10/2.51  
% 15.10/2.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.10/2.51  
% 15.10/2.51  
% 15.10/2.51  ------ 
% 15.10/2.51  Current options:
% 15.10/2.51  ------ 
% 15.10/2.51  
% 15.10/2.51  ------ Input Options
% 15.10/2.51  
% 15.10/2.51  --out_options                           all
% 15.10/2.51  --tptp_safe_out                         true
% 15.10/2.51  --problem_path                          ""
% 15.10/2.51  --include_path                          ""
% 15.10/2.51  --clausifier                            res/vclausify_rel
% 15.10/2.51  --clausifier_options                    ""
% 15.10/2.51  --stdin                                 false
% 15.10/2.51  --stats_out                             all
% 15.10/2.51  
% 15.10/2.51  ------ General Options
% 15.10/2.51  
% 15.10/2.51  --fof                                   false
% 15.10/2.51  --time_out_real                         305.
% 15.10/2.51  --time_out_virtual                      -1.
% 15.10/2.51  --symbol_type_check                     false
% 15.10/2.51  --clausify_out                          false
% 15.10/2.51  --sig_cnt_out                           false
% 15.10/2.51  --trig_cnt_out                          false
% 15.10/2.51  --trig_cnt_out_tolerance                1.
% 15.10/2.51  --trig_cnt_out_sk_spl                   false
% 15.10/2.51  --abstr_cl_out                          false
% 15.10/2.51  
% 15.10/2.51  ------ Global Options
% 15.10/2.51  
% 15.10/2.51  --schedule                              default
% 15.10/2.51  --add_important_lit                     false
% 15.10/2.51  --prop_solver_per_cl                    1000
% 15.10/2.51  --min_unsat_core                        false
% 15.10/2.51  --soft_assumptions                      false
% 15.10/2.51  --soft_lemma_size                       3
% 15.10/2.51  --prop_impl_unit_size                   0
% 15.10/2.51  --prop_impl_unit                        []
% 15.10/2.51  --share_sel_clauses                     true
% 15.10/2.51  --reset_solvers                         false
% 15.10/2.51  --bc_imp_inh                            [conj_cone]
% 15.10/2.51  --conj_cone_tolerance                   3.
% 15.10/2.51  --extra_neg_conj                        none
% 15.10/2.51  --large_theory_mode                     true
% 15.10/2.51  --prolific_symb_bound                   200
% 15.10/2.51  --lt_threshold                          2000
% 15.10/2.51  --clause_weak_htbl                      true
% 15.10/2.51  --gc_record_bc_elim                     false
% 15.10/2.51  
% 15.10/2.51  ------ Preprocessing Options
% 15.10/2.51  
% 15.10/2.51  --preprocessing_flag                    true
% 15.10/2.51  --time_out_prep_mult                    0.1
% 15.10/2.51  --splitting_mode                        input
% 15.10/2.51  --splitting_grd                         true
% 15.10/2.51  --splitting_cvd                         false
% 15.10/2.51  --splitting_cvd_svl                     false
% 15.10/2.51  --splitting_nvd                         32
% 15.10/2.51  --sub_typing                            true
% 15.10/2.51  --prep_gs_sim                           true
% 15.10/2.51  --prep_unflatten                        true
% 15.10/2.51  --prep_res_sim                          true
% 15.10/2.51  --prep_upred                            true
% 15.10/2.51  --prep_sem_filter                       exhaustive
% 15.10/2.51  --prep_sem_filter_out                   false
% 15.10/2.51  --pred_elim                             true
% 15.10/2.51  --res_sim_input                         true
% 15.10/2.51  --eq_ax_congr_red                       true
% 15.10/2.51  --pure_diseq_elim                       true
% 15.10/2.51  --brand_transform                       false
% 15.10/2.51  --non_eq_to_eq                          false
% 15.10/2.51  --prep_def_merge                        true
% 15.10/2.51  --prep_def_merge_prop_impl              false
% 15.10/2.51  --prep_def_merge_mbd                    true
% 15.10/2.51  --prep_def_merge_tr_red                 false
% 15.10/2.51  --prep_def_merge_tr_cl                  false
% 15.10/2.51  --smt_preprocessing                     true
% 15.10/2.51  --smt_ac_axioms                         fast
% 15.10/2.51  --preprocessed_out                      false
% 15.10/2.51  --preprocessed_stats                    false
% 15.10/2.51  
% 15.10/2.51  ------ Abstraction refinement Options
% 15.10/2.51  
% 15.10/2.51  --abstr_ref                             []
% 15.10/2.51  --abstr_ref_prep                        false
% 15.10/2.51  --abstr_ref_until_sat                   false
% 15.10/2.51  --abstr_ref_sig_restrict                funpre
% 15.10/2.51  --abstr_ref_af_restrict_to_split_sk     false
% 15.10/2.51  --abstr_ref_under                       []
% 15.10/2.51  
% 15.10/2.51  ------ SAT Options
% 15.10/2.51  
% 15.10/2.51  --sat_mode                              false
% 15.10/2.51  --sat_fm_restart_options                ""
% 15.10/2.51  --sat_gr_def                            false
% 15.10/2.51  --sat_epr_types                         true
% 15.10/2.51  --sat_non_cyclic_types                  false
% 15.10/2.51  --sat_finite_models                     false
% 15.10/2.51  --sat_fm_lemmas                         false
% 15.10/2.51  --sat_fm_prep                           false
% 15.10/2.51  --sat_fm_uc_incr                        true
% 15.10/2.51  --sat_out_model                         small
% 15.10/2.51  --sat_out_clauses                       false
% 15.10/2.51  
% 15.10/2.51  ------ QBF Options
% 15.10/2.51  
% 15.10/2.51  --qbf_mode                              false
% 15.10/2.51  --qbf_elim_univ                         false
% 15.10/2.51  --qbf_dom_inst                          none
% 15.10/2.51  --qbf_dom_pre_inst                      false
% 15.10/2.51  --qbf_sk_in                             false
% 15.10/2.51  --qbf_pred_elim                         true
% 15.10/2.51  --qbf_split                             512
% 15.10/2.51  
% 15.10/2.51  ------ BMC1 Options
% 15.10/2.51  
% 15.10/2.51  --bmc1_incremental                      false
% 15.10/2.51  --bmc1_axioms                           reachable_all
% 15.10/2.51  --bmc1_min_bound                        0
% 15.10/2.51  --bmc1_max_bound                        -1
% 15.10/2.51  --bmc1_max_bound_default                -1
% 15.10/2.51  --bmc1_symbol_reachability              true
% 15.10/2.51  --bmc1_property_lemmas                  false
% 15.10/2.51  --bmc1_k_induction                      false
% 15.10/2.51  --bmc1_non_equiv_states                 false
% 15.10/2.51  --bmc1_deadlock                         false
% 15.10/2.51  --bmc1_ucm                              false
% 15.10/2.51  --bmc1_add_unsat_core                   none
% 15.10/2.51  --bmc1_unsat_core_children              false
% 15.10/2.51  --bmc1_unsat_core_extrapolate_axioms    false
% 15.10/2.51  --bmc1_out_stat                         full
% 15.10/2.51  --bmc1_ground_init                      false
% 15.10/2.51  --bmc1_pre_inst_next_state              false
% 15.10/2.51  --bmc1_pre_inst_state                   false
% 15.10/2.51  --bmc1_pre_inst_reach_state             false
% 15.10/2.51  --bmc1_out_unsat_core                   false
% 15.10/2.51  --bmc1_aig_witness_out                  false
% 15.10/2.51  --bmc1_verbose                          false
% 15.10/2.51  --bmc1_dump_clauses_tptp                false
% 15.10/2.51  --bmc1_dump_unsat_core_tptp             false
% 15.10/2.51  --bmc1_dump_file                        -
% 15.10/2.51  --bmc1_ucm_expand_uc_limit              128
% 15.10/2.51  --bmc1_ucm_n_expand_iterations          6
% 15.10/2.51  --bmc1_ucm_extend_mode                  1
% 15.10/2.51  --bmc1_ucm_init_mode                    2
% 15.10/2.51  --bmc1_ucm_cone_mode                    none
% 15.10/2.51  --bmc1_ucm_reduced_relation_type        0
% 15.10/2.51  --bmc1_ucm_relax_model                  4
% 15.10/2.51  --bmc1_ucm_full_tr_after_sat            true
% 15.10/2.51  --bmc1_ucm_expand_neg_assumptions       false
% 15.10/2.51  --bmc1_ucm_layered_model                none
% 15.10/2.51  --bmc1_ucm_max_lemma_size               10
% 15.10/2.51  
% 15.10/2.51  ------ AIG Options
% 15.10/2.51  
% 15.10/2.51  --aig_mode                              false
% 15.10/2.51  
% 15.10/2.51  ------ Instantiation Options
% 15.10/2.51  
% 15.10/2.51  --instantiation_flag                    true
% 15.10/2.51  --inst_sos_flag                         true
% 15.10/2.51  --inst_sos_phase                        true
% 15.10/2.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.10/2.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.10/2.51  --inst_lit_sel_side                     none
% 15.10/2.51  --inst_solver_per_active                1400
% 15.10/2.51  --inst_solver_calls_frac                1.
% 15.10/2.51  --inst_passive_queue_type               priority_queues
% 15.10/2.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.10/2.51  --inst_passive_queues_freq              [25;2]
% 15.10/2.51  --inst_dismatching                      true
% 15.10/2.51  --inst_eager_unprocessed_to_passive     true
% 15.10/2.51  --inst_prop_sim_given                   true
% 15.10/2.51  --inst_prop_sim_new                     false
% 15.10/2.51  --inst_subs_new                         false
% 15.10/2.51  --inst_eq_res_simp                      false
% 15.10/2.51  --inst_subs_given                       false
% 15.10/2.51  --inst_orphan_elimination               true
% 15.10/2.51  --inst_learning_loop_flag               true
% 15.10/2.51  --inst_learning_start                   3000
% 15.10/2.51  --inst_learning_factor                  2
% 15.10/2.51  --inst_start_prop_sim_after_learn       3
% 15.10/2.51  --inst_sel_renew                        solver
% 15.10/2.51  --inst_lit_activity_flag                true
% 15.10/2.51  --inst_restr_to_given                   false
% 15.10/2.51  --inst_activity_threshold               500
% 15.10/2.51  --inst_out_proof                        true
% 15.10/2.51  
% 15.10/2.51  ------ Resolution Options
% 15.10/2.51  
% 15.10/2.51  --resolution_flag                       false
% 15.10/2.51  --res_lit_sel                           adaptive
% 15.10/2.51  --res_lit_sel_side                      none
% 15.10/2.51  --res_ordering                          kbo
% 15.10/2.51  --res_to_prop_solver                    active
% 15.10/2.51  --res_prop_simpl_new                    false
% 15.10/2.51  --res_prop_simpl_given                  true
% 15.10/2.51  --res_passive_queue_type                priority_queues
% 15.10/2.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.10/2.51  --res_passive_queues_freq               [15;5]
% 15.10/2.51  --res_forward_subs                      full
% 15.10/2.51  --res_backward_subs                     full
% 15.10/2.51  --res_forward_subs_resolution           true
% 15.10/2.51  --res_backward_subs_resolution          true
% 15.10/2.51  --res_orphan_elimination                true
% 15.10/2.51  --res_time_limit                        2.
% 15.10/2.51  --res_out_proof                         true
% 15.10/2.51  
% 15.10/2.51  ------ Superposition Options
% 15.10/2.51  
% 15.10/2.51  --superposition_flag                    true
% 15.10/2.51  --sup_passive_queue_type                priority_queues
% 15.10/2.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.10/2.51  --sup_passive_queues_freq               [8;1;4]
% 15.10/2.51  --demod_completeness_check              fast
% 15.10/2.51  --demod_use_ground                      true
% 15.10/2.51  --sup_to_prop_solver                    passive
% 15.10/2.51  --sup_prop_simpl_new                    true
% 15.10/2.51  --sup_prop_simpl_given                  true
% 15.10/2.51  --sup_fun_splitting                     true
% 15.10/2.51  --sup_smt_interval                      50000
% 15.10/2.51  
% 15.10/2.51  ------ Superposition Simplification Setup
% 15.10/2.51  
% 15.10/2.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.10/2.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.10/2.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.10/2.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.10/2.51  --sup_full_triv                         [TrivRules;PropSubs]
% 15.10/2.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.10/2.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.10/2.51  --sup_immed_triv                        [TrivRules]
% 15.10/2.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.10/2.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.10/2.51  --sup_immed_bw_main                     []
% 15.10/2.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.10/2.51  --sup_input_triv                        [Unflattening;TrivRules]
% 15.10/2.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.10/2.51  --sup_input_bw                          []
% 15.10/2.51  
% 15.10/2.51  ------ Combination Options
% 15.10/2.51  
% 15.10/2.51  --comb_res_mult                         3
% 15.10/2.51  --comb_sup_mult                         2
% 15.10/2.51  --comb_inst_mult                        10
% 15.10/2.51  
% 15.10/2.51  ------ Debug Options
% 15.10/2.51  
% 15.10/2.51  --dbg_backtrace                         false
% 15.10/2.51  --dbg_dump_prop_clauses                 false
% 15.10/2.51  --dbg_dump_prop_clauses_file            -
% 15.10/2.51  --dbg_out_stat                          false
% 15.10/2.51  
% 15.10/2.51  
% 15.10/2.51  
% 15.10/2.51  
% 15.10/2.51  ------ Proving...
% 15.10/2.51  
% 15.10/2.51  
% 15.10/2.51  % SZS status Theorem for theBenchmark.p
% 15.10/2.51  
% 15.10/2.51  % SZS output start CNFRefutation for theBenchmark.p
% 15.10/2.51  
% 15.10/2.51  fof(f1,axiom,(
% 15.10/2.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f27,plain,(
% 15.10/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 15.10/2.51    inference(cnf_transformation,[],[f1])).
% 15.10/2.51  
% 15.10/2.51  fof(f10,axiom,(
% 15.10/2.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f40,plain,(
% 15.10/2.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 15.10/2.51    inference(cnf_transformation,[],[f10])).
% 15.10/2.51  
% 15.10/2.51  fof(f6,axiom,(
% 15.10/2.51    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f36,plain,(
% 15.10/2.51    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 15.10/2.51    inference(cnf_transformation,[],[f6])).
% 15.10/2.51  
% 15.10/2.51  fof(f51,plain,(
% 15.10/2.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 15.10/2.51    inference(definition_unfolding,[],[f40,f36,f36])).
% 15.10/2.51  
% 15.10/2.51  fof(f11,axiom,(
% 15.10/2.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f41,plain,(
% 15.10/2.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.10/2.51    inference(cnf_transformation,[],[f11])).
% 15.10/2.51  
% 15.10/2.51  fof(f2,axiom,(
% 15.10/2.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f28,plain,(
% 15.10/2.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 15.10/2.51    inference(cnf_transformation,[],[f2])).
% 15.10/2.51  
% 15.10/2.51  fof(f8,axiom,(
% 15.10/2.51    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f38,plain,(
% 15.10/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 15.10/2.51    inference(cnf_transformation,[],[f8])).
% 15.10/2.51  
% 15.10/2.51  fof(f14,axiom,(
% 15.10/2.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f44,plain,(
% 15.10/2.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 15.10/2.51    inference(cnf_transformation,[],[f14])).
% 15.10/2.51  
% 15.10/2.51  fof(f47,plain,(
% 15.10/2.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 15.10/2.51    inference(definition_unfolding,[],[f44,f36])).
% 15.10/2.51  
% 15.10/2.51  fof(f50,plain,(
% 15.10/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 15.10/2.51    inference(definition_unfolding,[],[f38,f47])).
% 15.10/2.51  
% 15.10/2.51  fof(f15,conjecture,(
% 15.10/2.51    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f16,negated_conjecture,(
% 15.10/2.51    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 15.10/2.51    inference(negated_conjecture,[],[f15])).
% 15.10/2.51  
% 15.10/2.51  fof(f20,plain,(
% 15.10/2.51    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 15.10/2.51    inference(ennf_transformation,[],[f16])).
% 15.10/2.51  
% 15.10/2.51  fof(f25,plain,(
% 15.10/2.51    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)) & r1_tarski(sK1,k4_xboole_0(sK2,sK3)))),
% 15.10/2.51    introduced(choice_axiom,[])).
% 15.10/2.51  
% 15.10/2.51  fof(f26,plain,(
% 15.10/2.51    (~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)) & r1_tarski(sK1,k4_xboole_0(sK2,sK3))),
% 15.10/2.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f25])).
% 15.10/2.51  
% 15.10/2.51  fof(f45,plain,(
% 15.10/2.51    r1_tarski(sK1,k4_xboole_0(sK2,sK3))),
% 15.10/2.51    inference(cnf_transformation,[],[f26])).
% 15.10/2.51  
% 15.10/2.51  fof(f52,plain,(
% 15.10/2.51    r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))),
% 15.10/2.51    inference(definition_unfolding,[],[f45,f36])).
% 15.10/2.51  
% 15.10/2.51  fof(f9,axiom,(
% 15.10/2.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f19,plain,(
% 15.10/2.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 15.10/2.51    inference(ennf_transformation,[],[f9])).
% 15.10/2.51  
% 15.10/2.51  fof(f39,plain,(
% 15.10/2.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 15.10/2.51    inference(cnf_transformation,[],[f19])).
% 15.10/2.51  
% 15.10/2.51  fof(f12,axiom,(
% 15.10/2.51    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f42,plain,(
% 15.10/2.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 15.10/2.51    inference(cnf_transformation,[],[f12])).
% 15.10/2.51  
% 15.10/2.51  fof(f13,axiom,(
% 15.10/2.51    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f43,plain,(
% 15.10/2.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 15.10/2.51    inference(cnf_transformation,[],[f13])).
% 15.10/2.51  
% 15.10/2.51  fof(f7,axiom,(
% 15.10/2.51    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f37,plain,(
% 15.10/2.51    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 15.10/2.51    inference(cnf_transformation,[],[f7])).
% 15.10/2.51  
% 15.10/2.51  fof(f5,axiom,(
% 15.10/2.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f24,plain,(
% 15.10/2.51    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 15.10/2.51    inference(nnf_transformation,[],[f5])).
% 15.10/2.51  
% 15.10/2.51  fof(f34,plain,(
% 15.10/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 15.10/2.51    inference(cnf_transformation,[],[f24])).
% 15.10/2.51  
% 15.10/2.51  fof(f49,plain,(
% 15.10/2.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0) )),
% 15.10/2.51    inference(definition_unfolding,[],[f34,f36])).
% 15.10/2.51  
% 15.10/2.51  fof(f3,axiom,(
% 15.10/2.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 15.10/2.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.10/2.51  
% 15.10/2.51  fof(f21,plain,(
% 15.10/2.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 15.10/2.51    inference(nnf_transformation,[],[f3])).
% 15.10/2.51  
% 15.10/2.51  fof(f30,plain,(
% 15.10/2.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.10/2.51    inference(cnf_transformation,[],[f21])).
% 15.10/2.51  
% 15.10/2.51  fof(f46,plain,(
% 15.10/2.51    ~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)),
% 15.10/2.51    inference(cnf_transformation,[],[f26])).
% 15.10/2.51  
% 15.10/2.51  cnf(c_0,plain,
% 15.10/2.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 15.10/2.51      inference(cnf_transformation,[],[f27]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_12,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.10/2.51      inference(cnf_transformation,[],[f51]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1029,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_13,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.10/2.51      inference(cnf_transformation,[],[f41]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1,plain,
% 15.10/2.51      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 15.10/2.51      inference(cnf_transformation,[],[f28]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_849,plain,
% 15.10/2.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_13,c_1]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_10,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 15.10/2.51      inference(cnf_transformation,[],[f50]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_938,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_849,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1573,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_938]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_21904,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) = k3_xboole_0(X0,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1029,c_1573]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_17,negated_conjecture,
% 15.10/2.51      ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
% 15.10/2.51      inference(cnf_transformation,[],[f52]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_681,plain,
% 15.10/2.51      ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) = iProver_top ),
% 15.10/2.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_814,plain,
% 15.10/2.51      ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = iProver_top ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_0,c_681]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_11,plain,
% 15.10/2.51      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 15.10/2.51      inference(cnf_transformation,[],[f39]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_683,plain,
% 15.10/2.51      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 15.10/2.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1496,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = sK1 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_814,c_683]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1728,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1496,c_12]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_14,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 15.10/2.51      inference(cnf_transformation,[],[f42]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_705,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_14,c_1]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_4913,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X1,X0),X0))) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_705,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_12810,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) = k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1728,c_4913]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_703,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_14,c_1]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15,plain,
% 15.10/2.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.10/2.51      inference(cnf_transformation,[],[f43]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_950,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_15,c_14]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_957,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_950,c_849]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1097,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1,c_957]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1197,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1097,c_1097]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1398,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X2)) = k5_xboole_0(X1,X2) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1197,c_14]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9031,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_703,c_1398]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1193,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X1) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_957,c_1097]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1302,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X1,X2)) = k5_xboole_0(X0,X2) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1193,c_14]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_8706,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X1,X3)) = k5_xboole_0(X0,k5_xboole_0(X2,X3)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1302,c_1302]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9145,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_9031,c_8706]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_704,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_14,c_1]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_3713,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(X2,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1197,c_704]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_3736,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,X1) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_3713,c_14]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_10946,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(k5_xboole_0(X1,X3),X2) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_703,c_3736]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_11040,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X3)))) = k5_xboole_0(X1,k5_xboole_0(X3,X2)) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_10946,c_3736,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_13060,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_12810,c_9145,c_11040]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_939,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1819,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_14,c_1728]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_2011,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),X1)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1819,c_12]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9,plain,
% 15.10/2.51      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 15.10/2.51      inference(cnf_transformation,[],[f37]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_684,plain,
% 15.10/2.51      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 15.10/2.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1827,plain,
% 15.10/2.51      ( r1_tarski(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) = iProver_top ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1728,c_684]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1995,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1827,c_683]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_3084,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),X1)) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1995,c_12]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9434,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_2011,c_2011,c_3084]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9435,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1)))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_9434,c_2011,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9436,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,X1))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_9435,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9449,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1)))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_939,c_9436]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_8699,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X1,X2),X3)) = k5_xboole_0(k5_xboole_0(X0,X2),X3) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1302,c_14]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_3709,plain,
% 15.10/2.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_13,c_704]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_4923,plain,
% 15.10/2.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(X2,X0),X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_705,c_3709]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_4687,plain,
% 15.10/2.51      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X0,k5_xboole_0(X2,X1)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_3709,c_703]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_4939,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_4923,c_4687]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_8745,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X0,X3)))) = k5_xboole_0(X2,k5_xboole_0(X1,X3)) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_8699,c_4939]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9538,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_9449,c_8745,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_3727,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X2,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_704,c_957]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9539,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1)))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_9538,c_3727,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1105,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k3_xboole_0(X0,X0)) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_957,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1824,plain,
% 15.10/2.51      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1105,c_1728]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1043,plain,
% 15.10/2.51      ( r1_tarski(X0,X0) = iProver_top ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_10,c_684]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1498,plain,
% 15.10/2.51      ( k3_xboole_0(X0,X0) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1043,c_683]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1835,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_1824,c_15,c_1398,c_1496,c_1498]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1836,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k1_xboole_0) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_1835,c_15]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9540,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),X1)))))))) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_9539,c_15,c_1836]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15723,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)))),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))))))))) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_13060,c_9540]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1190,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,X0))) = k5_xboole_0(X1,X2) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_14,c_1097]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_7434,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X3,X0)))) = k5_xboole_0(X1,k5_xboole_0(X2,X3)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1190,c_703]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15728,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))))) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_15723,c_3727,c_7434,c_11040]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_5926,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))) = sK1 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1819,c_939]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_4926,plain,
% 15.10/2.51      ( k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X2))) = k5_xboole_0(X2,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_705,c_957]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_6045,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) = sK1 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_5926,c_4926]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15729,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_xboole_0) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_15728,c_15,c_6045,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_17483,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k1_xboole_0) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_15729]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_17579,plain,
% 15.10/2.51      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_17483,c_0]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1026,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19041,plain,
% 15.10/2.51      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),X1))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_17579,c_1026]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_953,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,X1)))))) = k5_xboole_0(X0,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_14,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_937,plain,
% 15.10/2.51      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_849,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1475,plain,
% 15.10/2.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_12,c_937]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9149,plain,
% 15.10/2.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X1)) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_1475]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15364,plain,
% 15.10/2.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)),X1)) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_9149]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9154,plain,
% 15.10/2.51      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1573,c_1475]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15398,plain,
% 15.10/2.51      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_15364,c_13,c_9154]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_17174,plain,
% 15.10/2.51      ( k3_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_953,c_15398]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19119,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_19041,c_849,c_17174]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_21916,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_21904,c_13,c_19119]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1099,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_12,c_957]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_33807,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)))) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)),X2) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_21916,c_1099]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_29495,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_21916,c_0]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34148,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)))) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_33807,c_29495]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19051,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1026,c_957]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_29475,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(k3_xboole_0(X1,X0),X2)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_21916,c_1029]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_29528,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_29475,c_1029]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34149,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X2,k3_xboole_0(X1,X0)) ),
% 15.10/2.51      inference(demodulation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_34148,c_1029,c_19051,c_29528]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_21810,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1105,c_1029]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_941,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_10,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_943,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k1_xboole_0)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_941,c_15]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_944,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_943,c_13]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19056,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))))),k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1026,c_944]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19072,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X3,k3_xboole_0(X0,X1)))) = k5_xboole_0(X2,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X3)))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1026,c_703]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19112,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))))),k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1))))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_19056,c_19072]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1276,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X0,X0))) = k3_xboole_0(X0,X0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1105,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1279,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0)) = k3_xboole_0(X0,X0) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_1276,c_15]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1280,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X0)) = k3_xboole_0(X0,X0) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_1279,c_13]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19113,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 15.10/2.51      inference(demodulation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_19112,c_1099,c_1280,c_1498]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_22000,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_21810,c_15,c_19113]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_29937,plain,
% 15.10/2.51      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k1_xboole_0))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_22000,c_1819]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_29938,plain,
% 15.10/2.51      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k1_xboole_0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_22000,c_1728]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1032,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),X3)) = k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X3) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_12,c_14]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_26358,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(k3_xboole_0(X0,X0),X1))),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1105,c_1032]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19007,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1573,c_1026]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19205,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_19007,c_19119]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19206,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_19205,c_13]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_26597,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X2) = k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 15.10/2.51      inference(light_normalisation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_26358,c_1498,c_19206]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_29950,plain,
% 15.10/2.51      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,sK3),k1_xboole_0))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_29938,c_26597]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_29951,plain,
% 15.10/2.51      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_29950,c_13]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_29952,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k1_xboole_0))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_29937,c_29951]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_29953,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) = sK1 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_29952,c_13,c_1496]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_33823,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(sK1,sK2),sK1) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK3) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_29953,c_1099]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34150,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(sK1,sK2),sK1) = k3_xboole_0(sK3,k3_xboole_0(sK2,sK1)) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_34149,c_33823]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19006,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1496,c_1026]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_19207,plain,
% 15.10/2.51      ( k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 15.10/2.51      inference(demodulation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_19006,c_1728,c_1819,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_20159,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(sK1,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_19207,c_1302]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_45817,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK3,k3_xboole_0(sK2,sK1))) = k5_xboole_0(sK1,sK1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_34150,c_20159]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_20165,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),X1) = k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),X1)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_19207,c_14]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15724,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_13060,c_9436]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15725,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_15724,c_8745]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15726,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_15725,c_3727]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_15727,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))))) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_15726,c_15,c_1836]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1188,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X0,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_12,c_1097]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_37550,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))),k1_xboole_0) = k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_15727,c_1188]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_33837,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1),k1_xboole_0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_15727,c_1099]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_33843,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_22000,c_1099]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34095,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_33843,c_29495]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34103,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),sK1),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_33837,c_34095]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_20125,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(X0,sK1)) = sK1 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_19207,c_1193]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_20896,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k3_xboole_0(sK1,sK1),sK1)) = sK1 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1105,c_20125]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1495,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_684,c_683]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_20997,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,sK1) = sK1 ),
% 15.10/2.51      inference(demodulation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_20896,c_15,c_849,c_1495,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_22079,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_20997,c_1026]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34104,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
% 15.10/2.51      inference(light_normalisation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_34103,c_1995,c_22079]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_37845,plain,
% 15.10/2.51      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k1_xboole_0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 15.10/2.51      inference(light_normalisation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_37550,c_1995,c_34104]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1033,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0))))) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_12,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_33826,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X0),k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X0,X0),X0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1033,c_1099]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34123,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k1_xboole_0 ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_33826,c_15,c_1498]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34562,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_34123]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1820,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(X0,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_1728]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_38438,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_34562,c_1820]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_38445,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK2,sK3),k1_xboole_0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_38438,c_26597]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_38446,plain,
% 15.10/2.51      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = sK1 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_38445,c_1496,c_34095]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_2627,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_703,c_10]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_10495,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k3_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_2627,c_9436]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_10496,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k3_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)))))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_10495,c_8745,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_10497,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k3_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_10496,c_3727,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_10498,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k3_xboole_0(X1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))))))) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_10497,c_15,c_1836]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_11719,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))))))) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1819,c_10498]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_39765,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),sK3),sK1))))))) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_38446,c_11719]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_20126,plain,
% 15.10/2.51      ( k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k3_xboole_0(X0,sK1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_19207,c_957]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9451,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k1_xboole_0))))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))))) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1573,c_9436]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9531,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))),k1_xboole_0)))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0),k5_xboole_0(k3_xboole_0(sK3,sK2),k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_9451,c_8745,c_9145]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9532,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_9531,c_3727,c_9145,c_9436]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9533,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k5_xboole_0(sK1,k1_xboole_0)))) = k3_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK3,sK2),k3_xboole_0(sK3,sK2))) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_9532,c_1836]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9534,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(sK1,X0)) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_9533,c_13,c_15,c_957,c_1836,c_1995]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_9705,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(X0,sK1)),k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_9534]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_20148,plain,
% 15.10/2.51      ( k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_19207,c_9705]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_21356,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_20148,c_0]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_33842,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),sK1),X0) = k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),sK1),k1_xboole_0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_21356,c_1099]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34096,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),sK1),X0) = k3_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_33842,c_34095]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1041,plain,
% 15.10/2.51      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_684]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_1497,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1041,c_683]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_21358,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))) = k5_xboole_0(k3_xboole_0(X0,sK1),k1_xboole_0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_20148,c_1026]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_3088,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_1995,c_0]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_21360,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k3_xboole_0(X0,sK1)) = k5_xboole_0(k3_xboole_0(X0,sK1),k1_xboole_0) ),
% 15.10/2.51      inference(light_normalisation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_21358,c_3088,c_20126]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_21361,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k3_xboole_0(X0,sK1)) = k3_xboole_0(X0,sK1) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_21360,c_13]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_22536,plain,
% 15.10/2.51      ( k3_xboole_0(X0,k3_xboole_0(sK1,X0)) = k3_xboole_0(X0,sK1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_21361]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_23769,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X0,sK1)))) = k3_xboole_0(sK1,X0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_22536,c_2627]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_21076,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X0,sK1)) = k5_xboole_0(sK1,sK1) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_20126,c_1190]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_21084,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_21076,c_15]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_23955,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(sK1,X0),X0) = k3_xboole_0(sK1,X0) ),
% 15.10/2.51      inference(light_normalisation,[status(thm)],[c_23769,c_13,c_21084]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_24439,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,sK1),X0) = k3_xboole_0(sK1,X0) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_0,c_23955]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_34097,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,X0) ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_34096,c_1497,c_24439]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_39818,plain,
% 15.10/2.51      ( k3_xboole_0(sK1,sK3) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_39765,c_1819,c_7434,c_20126,c_22079,c_34097]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_40053,plain,
% 15.10/2.51      ( k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,k5_xboole_0(sK1,k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,sK1),sK3) ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_39818,c_1099]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_40225,plain,
% 15.10/2.51      ( k3_xboole_0(k3_xboole_0(X0,sK1),sK3) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,[status(thm)],[c_40053,c_13,c_15]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_42448,plain,
% 15.10/2.51      ( k3_xboole_0(sK3,k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
% 15.10/2.51      inference(superposition,[status(thm)],[c_40225,c_0]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_46032,plain,
% 15.10/2.51      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 15.10/2.51      inference(demodulation,
% 15.10/2.51                [status(thm)],
% 15.10/2.51                [c_45817,c_15,c_20165,c_37845,c_42448]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_8,plain,
% 15.10/2.51      ( r1_tarski(X0,X1)
% 15.10/2.51      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 15.10/2.51      inference(cnf_transformation,[],[f49]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_709,plain,
% 15.10/2.51      ( r1_tarski(sK1,sK2)
% 15.10/2.51      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k1_xboole_0 ),
% 15.10/2.51      inference(instantiation,[status(thm)],[c_8]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_2,plain,
% 15.10/2.51      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.10/2.51      inference(cnf_transformation,[],[f30]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_103,plain,
% 15.10/2.51      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 15.10/2.51      inference(prop_impl,[status(thm)],[c_2]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_16,negated_conjecture,
% 15.10/2.51      ( ~ r1_tarski(sK1,sK2) | ~ r1_xboole_0(sK1,sK3) ),
% 15.10/2.51      inference(cnf_transformation,[],[f46]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_343,plain,
% 15.10/2.51      ( ~ r1_tarski(sK1,sK2)
% 15.10/2.51      | k3_xboole_0(X0,X1) != k1_xboole_0
% 15.10/2.51      | sK3 != X1
% 15.10/2.51      | sK1 != X0 ),
% 15.10/2.51      inference(resolution_lifted,[status(thm)],[c_103,c_16]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(c_344,plain,
% 15.10/2.51      ( ~ r1_tarski(sK1,sK2) | k3_xboole_0(sK1,sK3) != k1_xboole_0 ),
% 15.10/2.51      inference(unflattening,[status(thm)],[c_343]) ).
% 15.10/2.51  
% 15.10/2.51  cnf(contradiction,plain,
% 15.10/2.51      ( $false ),
% 15.10/2.51      inference(minisat,[status(thm)],[c_46032,c_39818,c_709,c_344]) ).
% 15.10/2.51  
% 15.10/2.51  
% 15.10/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.10/2.51  
% 15.10/2.51  ------                               Statistics
% 15.10/2.51  
% 15.10/2.51  ------ General
% 15.10/2.51  
% 15.10/2.51  abstr_ref_over_cycles:                  0
% 15.10/2.51  abstr_ref_under_cycles:                 0
% 15.10/2.51  gc_basic_clause_elim:                   0
% 15.10/2.51  forced_gc_time:                         0
% 15.10/2.51  parsing_time:                           0.009
% 15.10/2.51  unif_index_cands_time:                  0.
% 15.10/2.51  unif_index_add_time:                    0.
% 15.10/2.51  orderings_time:                         0.
% 15.10/2.51  out_proof_time:                         0.017
% 15.10/2.51  total_time:                             1.587
% 15.10/2.51  num_of_symbols:                         41
% 15.10/2.51  num_of_terms:                           76510
% 15.10/2.51  
% 15.10/2.51  ------ Preprocessing
% 15.10/2.51  
% 15.10/2.51  num_of_splits:                          0
% 15.10/2.51  num_of_split_atoms:                     0
% 15.10/2.51  num_of_reused_defs:                     0
% 15.10/2.51  num_eq_ax_congr_red:                    6
% 15.10/2.51  num_of_sem_filtered_clauses:            1
% 15.10/2.51  num_of_subtypes:                        0
% 15.10/2.51  monotx_restored_types:                  0
% 15.10/2.51  sat_num_of_epr_types:                   0
% 15.10/2.51  sat_num_of_non_cyclic_types:            0
% 15.10/2.51  sat_guarded_non_collapsed_types:        0
% 15.10/2.51  num_pure_diseq_elim:                    0
% 15.10/2.51  simp_replaced_by:                       0
% 15.10/2.51  res_preprocessed:                       69
% 15.10/2.51  prep_upred:                             0
% 15.10/2.51  prep_unflattend:                        23
% 15.10/2.51  smt_new_axioms:                         0
% 15.10/2.51  pred_elim_cands:                        3
% 15.10/2.51  pred_elim:                              0
% 15.10/2.51  pred_elim_cl:                           0
% 15.10/2.51  pred_elim_cycles:                       2
% 15.10/2.51  merged_defs:                            12
% 15.10/2.51  merged_defs_ncl:                        0
% 15.10/2.51  bin_hyper_res:                          12
% 15.10/2.51  prep_cycles:                            3
% 15.10/2.51  pred_elim_time:                         0.002
% 15.10/2.51  splitting_time:                         0.
% 15.10/2.51  sem_filter_time:                        0.
% 15.10/2.51  monotx_time:                            0.
% 15.10/2.51  subtype_inf_time:                       0.
% 15.10/2.51  
% 15.10/2.51  ------ Problem properties
% 15.10/2.51  
% 15.10/2.51  clauses:                                18
% 15.10/2.51  conjectures:                            2
% 15.10/2.51  epr:                                    2
% 15.10/2.51  horn:                                   16
% 15.10/2.51  ground:                                 2
% 15.10/2.51  unary:                                  9
% 15.10/2.51  binary:                                 8
% 15.10/2.51  lits:                                   28
% 15.10/2.51  lits_eq:                                12
% 15.10/2.51  fd_pure:                                0
% 15.10/2.51  fd_pseudo:                              0
% 15.10/2.51  fd_cond:                                0
% 15.10/2.51  fd_pseudo_cond:                         0
% 15.10/2.51  ac_symbols:                             1
% 15.10/2.51  
% 15.10/2.51  ------ Propositional Solver
% 15.10/2.51  
% 15.10/2.51  prop_solver_calls:                      30
% 15.10/2.51  prop_fast_solver_calls:                 609
% 15.10/2.51  smt_solver_calls:                       0
% 15.10/2.51  smt_fast_solver_calls:                  0
% 15.10/2.51  prop_num_of_clauses:                    15533
% 15.10/2.51  prop_preprocess_simplified:             18098
% 15.10/2.51  prop_fo_subsumed:                       0
% 15.10/2.51  prop_solver_time:                       0.
% 15.10/2.51  smt_solver_time:                        0.
% 15.10/2.51  smt_fast_solver_time:                   0.
% 15.10/2.51  prop_fast_solver_time:                  0.
% 15.10/2.51  prop_unsat_core_time:                   0.001
% 15.10/2.51  
% 15.10/2.51  ------ QBF
% 15.10/2.51  
% 15.10/2.51  qbf_q_res:                              0
% 15.10/2.51  qbf_num_tautologies:                    0
% 15.10/2.51  qbf_prep_cycles:                        0
% 15.10/2.51  
% 15.10/2.51  ------ BMC1
% 15.10/2.51  
% 15.10/2.51  bmc1_current_bound:                     -1
% 15.10/2.51  bmc1_last_solved_bound:                 -1
% 15.10/2.51  bmc1_unsat_core_size:                   -1
% 15.10/2.51  bmc1_unsat_core_parents_size:           -1
% 15.10/2.51  bmc1_merge_next_fun:                    0
% 15.10/2.51  bmc1_unsat_core_clauses_time:           0.
% 15.10/2.51  
% 15.10/2.51  ------ Instantiation
% 15.10/2.51  
% 15.10/2.51  inst_num_of_clauses:                    3498
% 15.10/2.51  inst_num_in_passive:                    959
% 15.10/2.51  inst_num_in_active:                     1186
% 15.10/2.51  inst_num_in_unprocessed:                1353
% 15.10/2.51  inst_num_of_loops:                      1250
% 15.10/2.51  inst_num_of_learning_restarts:          0
% 15.10/2.51  inst_num_moves_active_passive:          59
% 15.10/2.51  inst_lit_activity:                      0
% 15.10/2.51  inst_lit_activity_moves:                0
% 15.10/2.51  inst_num_tautologies:                   0
% 15.10/2.51  inst_num_prop_implied:                  0
% 15.10/2.51  inst_num_existing_simplified:           0
% 15.10/2.51  inst_num_eq_res_simplified:             0
% 15.10/2.51  inst_num_child_elim:                    0
% 15.10/2.51  inst_num_of_dismatching_blockings:      1217
% 15.10/2.51  inst_num_of_non_proper_insts:           3538
% 15.10/2.51  inst_num_of_duplicates:                 0
% 15.10/2.51  inst_inst_num_from_inst_to_res:         0
% 15.10/2.51  inst_dismatching_checking_time:         0.
% 15.10/2.51  
% 15.10/2.51  ------ Resolution
% 15.10/2.51  
% 15.10/2.51  res_num_of_clauses:                     0
% 15.10/2.51  res_num_in_passive:                     0
% 15.10/2.51  res_num_in_active:                      0
% 15.10/2.51  res_num_of_loops:                       72
% 15.10/2.51  res_forward_subset_subsumed:            711
% 15.10/2.51  res_backward_subset_subsumed:           0
% 15.10/2.51  res_forward_subsumed:                   0
% 15.10/2.51  res_backward_subsumed:                  0
% 15.10/2.51  res_forward_subsumption_resolution:     0
% 15.10/2.51  res_backward_subsumption_resolution:    0
% 15.10/2.51  res_clause_to_clause_subsumption:       40606
% 15.10/2.51  res_orphan_elimination:                 0
% 15.10/2.51  res_tautology_del:                      369
% 15.10/2.51  res_num_eq_res_simplified:              0
% 15.10/2.51  res_num_sel_changes:                    0
% 15.10/2.51  res_moves_from_active_to_pass:          0
% 15.10/2.51  
% 15.10/2.51  ------ Superposition
% 15.10/2.51  
% 15.10/2.51  sup_time_total:                         0.
% 15.10/2.51  sup_time_generating:                    0.
% 15.10/2.51  sup_time_sim_full:                      0.
% 15.10/2.51  sup_time_sim_immed:                     0.
% 15.10/2.51  
% 15.10/2.51  sup_num_of_clauses:                     3422
% 15.10/2.51  sup_num_in_active:                      227
% 15.10/2.51  sup_num_in_passive:                     3195
% 15.10/2.51  sup_num_of_loops:                       248
% 15.10/2.51  sup_fw_superposition:                   7331
% 15.10/2.51  sup_bw_superposition:                   7270
% 15.10/2.51  sup_immediate_simplified:               8195
% 15.10/2.51  sup_given_eliminated:                   9
% 15.10/2.51  comparisons_done:                       0
% 15.10/2.51  comparisons_avoided:                    0
% 15.10/2.51  
% 15.10/2.51  ------ Simplifications
% 15.10/2.51  
% 15.10/2.51  
% 15.10/2.51  sim_fw_subset_subsumed:                 46
% 15.10/2.51  sim_bw_subset_subsumed:                 0
% 15.10/2.51  sim_fw_subsumed:                        773
% 15.10/2.51  sim_bw_subsumed:                        31
% 15.10/2.51  sim_fw_subsumption_res:                 0
% 15.10/2.51  sim_bw_subsumption_res:                 0
% 15.10/2.51  sim_tautology_del:                      0
% 15.10/2.51  sim_eq_tautology_del:                   2778
% 15.10/2.51  sim_eq_res_simp:                        112
% 15.10/2.51  sim_fw_demodulated:                     7672
% 15.10/2.51  sim_bw_demodulated:                     140
% 15.10/2.51  sim_light_normalised:                   3633
% 15.10/2.51  sim_joinable_taut:                      89
% 15.10/2.51  sim_joinable_simp:                      0
% 15.10/2.51  sim_ac_normalised:                      0
% 15.10/2.51  sim_smt_subsumption:                    0
% 15.10/2.51  
%------------------------------------------------------------------------------
