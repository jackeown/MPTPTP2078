%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:40 EST 2020

% Result     : Theorem 27.02s
% Output     : CNFRefutation 27.02s
% Verified   : 
% Statistics : Number of formulae       :  112 (24961 expanded)
%              Number of clauses        :   83 (8626 expanded)
%              Number of leaves         :   10 (6678 expanded)
%              Depth                    :   33
%              Number of atoms          :  113 (24962 expanded)
%              Number of equality atoms :  112 (24961 expanded)
%              Maximal formula depth    :   11 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k1_tarski(X4)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))) ),
    inference(definition_unfolding,[],[f20,f24,f26])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f15,f17,f17])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f21,f26,f23])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
   => k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f12])).

fof(f22,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k2_tarski(X5,X6),k1_tarski(X7)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f16,f24,f24])).

fof(f29,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) ),
    inference(definition_unfolding,[],[f22,f23,f25])).

cnf(c_0,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_15,plain,
    ( k2_xboole_0(k2_xboole_0(X0_39,X1_39),X2_39) = k2_xboole_0(X0_39,k2_xboole_0(X1_39,X2_39)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_14,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k1_tarski(X4_40)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_29,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))) ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_31,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))) ),
    inference(superposition,[status(thm)],[c_15,c_29])).

cnf(c_34,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40))),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
    inference(superposition,[status(thm)],[c_31,c_15])).

cnf(c_28,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k1_tarski(X4_40),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
    inference(superposition,[status(thm)],[c_14,c_15])).

cnf(c_39,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40))),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k1_tarski(X4_40),X0_39)) ),
    inference(light_normalisation,[status(thm)],[c_28,c_34])).

cnf(c_46,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40))),X0_39)) ),
    inference(superposition,[status(thm)],[c_39,c_15])).

cnf(c_55,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
    inference(light_normalisation,[status(thm)],[c_34,c_34,c_46])).

cnf(c_2,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),k1_tarski(X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_13,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),k1_tarski(X5_40)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_59,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40)))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
    inference(superposition,[status(thm)],[c_55,c_13])).

cnf(c_88,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40))))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
    inference(superposition,[status(thm)],[c_15,c_59])).

cnf(c_61,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39)) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) ),
    inference(superposition,[status(thm)],[c_55,c_15])).

cnf(c_68,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) ),
    inference(superposition,[status(thm)],[c_15,c_46])).

cnf(c_91,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39)) ),
    inference(light_normalisation,[status(thm)],[c_61,c_61,c_68])).

cnf(c_96,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39),X1_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))),X1_39) ),
    inference(superposition,[status(thm)],[c_91,c_15])).

cnf(c_47,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k1_tarski(X4_40),X0_39)) ),
    inference(demodulation,[status(thm)],[c_46,c_39])).

cnf(c_73,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k1_tarski(X4_40),X0_39)) ),
    inference(light_normalisation,[status(thm)],[c_47,c_47,c_68])).

cnf(c_80,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))),X1_39) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)) ),
    inference(superposition,[status(thm)],[c_73,c_15])).

cnf(c_94,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))) ),
    inference(superposition,[status(thm)],[c_15,c_91])).

cnf(c_109,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))),X1_39) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39),X1_39)) ),
    inference(light_normalisation,[status(thm)],[c_96,c_80,c_94])).

cnf(c_104,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) ),
    inference(light_normalisation,[status(thm)],[c_68,c_68,c_94])).

cnf(c_106,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
    inference(demodulation,[status(thm)],[c_104,c_55])).

cnf(c_242,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))),X1_39) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),k2_xboole_0(X0_39,X1_39)) ),
    inference(superposition,[status(thm)],[c_106,c_15])).

cnf(c_245,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))),X1_39) ),
    inference(demodulation,[status(thm)],[c_242,c_106])).

cnf(c_348,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39),X1_39)) ),
    inference(light_normalisation,[status(thm)],[c_109,c_245])).

cnf(c_352,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39)),X1_39)) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
    inference(superposition,[status(thm)],[c_15,c_348])).

cnf(c_1065,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39),X1_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
    inference(superposition,[status(thm)],[c_15,c_352])).

cnf(c_2347,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),X0_39)),X1_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
    inference(superposition,[status(thm)],[c_15,c_1065])).

cnf(c_3189,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
    inference(superposition,[status(thm)],[c_15,c_2347])).

cnf(c_939,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),X0_39)))),X1_39) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
    inference(superposition,[status(thm)],[c_15,c_245])).

cnf(c_3578,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),X0_39)))),X1_39) ),
    inference(demodulation,[status(thm)],[c_3189,c_939])).

cnf(c_3599,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) ),
    inference(superposition,[status(thm)],[c_15,c_3189])).

cnf(c_5655,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),X0_39)))),X1_39) ),
    inference(light_normalisation,[status(thm)],[c_3578,c_3578,c_3599])).

cnf(c_5659,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_xboole_0(k1_tarski(X5_40),k1_tarski(X6_40)),X0_39))))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39) ),
    inference(superposition,[status(thm)],[c_88,c_5655])).

cnf(c_36,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),k2_xboole_0(k1_tarski(X5_40),X0_39)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
    inference(superposition,[status(thm)],[c_13,c_15])).

cnf(c_140,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),k2_xboole_0(k1_tarski(X5_40),X0_39))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
    inference(superposition,[status(thm)],[c_36,c_15])).

cnf(c_100,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39)) ),
    inference(demodulation,[status(thm)],[c_94,c_91])).

cnf(c_141,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40)),X0_39)))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
    inference(demodulation,[status(thm)],[c_140,c_73,c_100])).

cnf(c_142,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40)),X0_39)))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
    inference(demodulation,[status(thm)],[c_141,c_94])).

cnf(c_369,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),k1_tarski(X6_40)) ),
    inference(superposition,[status(thm)],[c_29,c_142])).

cnf(c_37,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),k1_tarski(X5_40))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
    inference(superposition,[status(thm)],[c_13,c_15])).

cnf(c_38,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
    inference(demodulation,[status(thm)],[c_37,c_14])).

cnf(c_390,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),k1_tarski(X6_40)) ),
    inference(demodulation,[status(thm)],[c_369,c_38])).

cnf(c_1209,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40)))),k1_tarski(X6_40)) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) ),
    inference(superposition,[status(thm)],[c_15,c_390])).

cnf(c_2557,plain,
    ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),k1_tarski(X6_40))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) ),
    inference(superposition,[status(thm)],[c_1209,c_15])).

cnf(c_2558,plain,
    ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) ),
    inference(demodulation,[status(thm)],[c_2557,c_14])).

cnf(c_3395,plain,
    ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39) ),
    inference(superposition,[status(thm)],[c_2558,c_15])).

cnf(c_1213,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40)),k1_tarski(X6_40))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) ),
    inference(superposition,[status(thm)],[c_390,c_15])).

cnf(c_2576,plain,
    ( k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40)),k1_tarski(X6_40)),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39) ),
    inference(superposition,[status(thm)],[c_1213,c_15])).

cnf(c_3406,plain,
    ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)),X0_39)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39) ),
    inference(demodulation,[status(thm)],[c_3395,c_106,c_2576])).

cnf(c_5805,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_xboole_0(k1_tarski(X5_40),k1_tarski(X6_40)),X0_39))))) = k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)),X0_39)))) ),
    inference(light_normalisation,[status(thm)],[c_5659,c_3406])).

cnf(c_89,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40))),X0_39)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
    inference(superposition,[status(thm)],[c_59,c_15])).

cnf(c_325,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40)),X0_39))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
    inference(superposition,[status(thm)],[c_15,c_89])).

cnf(c_647,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40)),X0_39)))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
    inference(superposition,[status(thm)],[c_15,c_325])).

cnf(c_5806,plain,
    ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)),X0_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40))),X0_39)) ),
    inference(demodulation,[status(thm)],[c_5805,c_647])).

cnf(c_40199,plain,
    ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40)))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40))),k1_tarski(X7_40))) ),
    inference(superposition,[status(thm)],[c_29,c_5806])).

cnf(c_32,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
    inference(superposition,[status(thm)],[c_29,c_15])).

cnf(c_48,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39)) ),
    inference(light_normalisation,[status(thm)],[c_32,c_34,c_46])).

cnf(c_51,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39),X1_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))),X1_39) ),
    inference(superposition,[status(thm)],[c_48,c_15])).

cnf(c_60,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),k2_xboole_0(X0_39,X1_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))),X1_39) ),
    inference(superposition,[status(thm)],[c_55,c_15])).

cnf(c_62,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))),X1_39) ),
    inference(demodulation,[status(thm)],[c_60,c_55])).

cnf(c_197,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39),X1_39)) ),
    inference(light_normalisation,[status(thm)],[c_51,c_62])).

cnf(c_198,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39),X1_39)) ),
    inference(demodulation,[status(thm)],[c_197,c_104])).

cnf(c_201,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39)),X1_39)) ),
    inference(superposition,[status(thm)],[c_15,c_198])).

cnf(c_510,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
    inference(superposition,[status(thm)],[c_15,c_201])).

cnf(c_1460,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
    inference(superposition,[status(thm)],[c_15,c_510])).

cnf(c_3574,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) ),
    inference(demodulation,[status(thm)],[c_3189,c_1460])).

cnf(c_4004,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) ),
    inference(light_normalisation,[status(thm)],[c_3574,c_3574,c_3599])).

cnf(c_4010,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) ),
    inference(superposition,[status(thm)],[c_15,c_4004])).

cnf(c_4831,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40)))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40))))) ),
    inference(superposition,[status(thm)],[c_2558,c_4010])).

cnf(c_40411,plain,
    ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40)))))) = k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40)))) ),
    inference(demodulation,[status(thm)],[c_40199,c_38,c_390,c_4831])).

cnf(c_3,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_12,negated_conjecture,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_24,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) ),
    inference(demodulation,[status(thm)],[c_15,c_12])).

cnf(c_25,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) ),
    inference(superposition,[status(thm)],[c_15,c_24])).

cnf(c_105,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) ),
    inference(demodulation,[status(thm)],[c_104,c_25])).

cnf(c_131,plain,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) ),
    inference(superposition,[status(thm)],[c_15,c_105])).

cnf(c_70249,plain,
    ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) ),
    inference(demodulation,[status(thm)],[c_40411,c_131])).

cnf(c_70685,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_15,c_70249])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:35:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.02/3.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.02/3.99  
% 27.02/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.02/3.99  
% 27.02/3.99  ------  iProver source info
% 27.02/3.99  
% 27.02/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.02/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.02/3.99  git: non_committed_changes: false
% 27.02/3.99  git: last_make_outside_of_git: false
% 27.02/3.99  
% 27.02/3.99  ------ 
% 27.02/3.99  
% 27.02/3.99  ------ Input Options
% 27.02/3.99  
% 27.02/3.99  --out_options                           all
% 27.02/3.99  --tptp_safe_out                         true
% 27.02/3.99  --problem_path                          ""
% 27.02/3.99  --include_path                          ""
% 27.02/3.99  --clausifier                            res/vclausify_rel
% 27.02/3.99  --clausifier_options                    --mode clausify
% 27.02/3.99  --stdin                                 false
% 27.02/3.99  --stats_out                             all
% 27.02/3.99  
% 27.02/3.99  ------ General Options
% 27.02/3.99  
% 27.02/3.99  --fof                                   false
% 27.02/3.99  --time_out_real                         305.
% 27.02/3.99  --time_out_virtual                      -1.
% 27.02/3.99  --symbol_type_check                     false
% 27.02/3.99  --clausify_out                          false
% 27.02/3.99  --sig_cnt_out                           false
% 27.02/3.99  --trig_cnt_out                          false
% 27.02/3.99  --trig_cnt_out_tolerance                1.
% 27.02/3.99  --trig_cnt_out_sk_spl                   false
% 27.02/3.99  --abstr_cl_out                          false
% 27.02/3.99  
% 27.02/3.99  ------ Global Options
% 27.02/3.99  
% 27.02/3.99  --schedule                              default
% 27.02/3.99  --add_important_lit                     false
% 27.02/3.99  --prop_solver_per_cl                    1000
% 27.02/3.99  --min_unsat_core                        false
% 27.02/3.99  --soft_assumptions                      false
% 27.02/3.99  --soft_lemma_size                       3
% 27.02/3.99  --prop_impl_unit_size                   0
% 27.02/3.99  --prop_impl_unit                        []
% 27.02/3.99  --share_sel_clauses                     true
% 27.02/3.99  --reset_solvers                         false
% 27.02/3.99  --bc_imp_inh                            [conj_cone]
% 27.02/3.99  --conj_cone_tolerance                   3.
% 27.02/3.99  --extra_neg_conj                        none
% 27.02/3.99  --large_theory_mode                     true
% 27.02/3.99  --prolific_symb_bound                   200
% 27.02/3.99  --lt_threshold                          2000
% 27.02/3.99  --clause_weak_htbl                      true
% 27.02/3.99  --gc_record_bc_elim                     false
% 27.02/3.99  
% 27.02/3.99  ------ Preprocessing Options
% 27.02/3.99  
% 27.02/3.99  --preprocessing_flag                    true
% 27.02/3.99  --time_out_prep_mult                    0.1
% 27.02/3.99  --splitting_mode                        input
% 27.02/3.99  --splitting_grd                         true
% 27.02/3.99  --splitting_cvd                         false
% 27.02/3.99  --splitting_cvd_svl                     false
% 27.02/3.99  --splitting_nvd                         32
% 27.02/3.99  --sub_typing                            true
% 27.02/3.99  --prep_gs_sim                           true
% 27.02/3.99  --prep_unflatten                        true
% 27.02/3.99  --prep_res_sim                          true
% 27.02/3.99  --prep_upred                            true
% 27.02/3.99  --prep_sem_filter                       exhaustive
% 27.02/3.99  --prep_sem_filter_out                   false
% 27.02/3.99  --pred_elim                             true
% 27.02/3.99  --res_sim_input                         true
% 27.02/3.99  --eq_ax_congr_red                       true
% 27.02/3.99  --pure_diseq_elim                       true
% 27.02/3.99  --brand_transform                       false
% 27.02/3.99  --non_eq_to_eq                          false
% 27.02/3.99  --prep_def_merge                        true
% 27.02/3.99  --prep_def_merge_prop_impl              false
% 27.02/3.99  --prep_def_merge_mbd                    true
% 27.02/3.99  --prep_def_merge_tr_red                 false
% 27.02/3.99  --prep_def_merge_tr_cl                  false
% 27.02/3.99  --smt_preprocessing                     true
% 27.02/3.99  --smt_ac_axioms                         fast
% 27.02/3.99  --preprocessed_out                      false
% 27.02/3.99  --preprocessed_stats                    false
% 27.02/3.99  
% 27.02/3.99  ------ Abstraction refinement Options
% 27.02/3.99  
% 27.02/3.99  --abstr_ref                             []
% 27.02/3.99  --abstr_ref_prep                        false
% 27.02/3.99  --abstr_ref_until_sat                   false
% 27.02/3.99  --abstr_ref_sig_restrict                funpre
% 27.02/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.02/3.99  --abstr_ref_under                       []
% 27.02/3.99  
% 27.02/3.99  ------ SAT Options
% 27.02/3.99  
% 27.02/3.99  --sat_mode                              false
% 27.02/3.99  --sat_fm_restart_options                ""
% 27.02/3.99  --sat_gr_def                            false
% 27.02/3.99  --sat_epr_types                         true
% 27.02/3.99  --sat_non_cyclic_types                  false
% 27.02/3.99  --sat_finite_models                     false
% 27.02/3.99  --sat_fm_lemmas                         false
% 27.02/3.99  --sat_fm_prep                           false
% 27.02/3.99  --sat_fm_uc_incr                        true
% 27.02/3.99  --sat_out_model                         small
% 27.02/3.99  --sat_out_clauses                       false
% 27.02/3.99  
% 27.02/3.99  ------ QBF Options
% 27.02/3.99  
% 27.02/3.99  --qbf_mode                              false
% 27.02/3.99  --qbf_elim_univ                         false
% 27.02/3.99  --qbf_dom_inst                          none
% 27.02/3.99  --qbf_dom_pre_inst                      false
% 27.02/3.99  --qbf_sk_in                             false
% 27.02/3.99  --qbf_pred_elim                         true
% 27.02/3.99  --qbf_split                             512
% 27.02/3.99  
% 27.02/3.99  ------ BMC1 Options
% 27.02/3.99  
% 27.02/3.99  --bmc1_incremental                      false
% 27.02/3.99  --bmc1_axioms                           reachable_all
% 27.02/3.99  --bmc1_min_bound                        0
% 27.02/3.99  --bmc1_max_bound                        -1
% 27.02/3.99  --bmc1_max_bound_default                -1
% 27.02/3.99  --bmc1_symbol_reachability              true
% 27.02/3.99  --bmc1_property_lemmas                  false
% 27.02/3.99  --bmc1_k_induction                      false
% 27.02/3.99  --bmc1_non_equiv_states                 false
% 27.02/3.99  --bmc1_deadlock                         false
% 27.02/3.99  --bmc1_ucm                              false
% 27.02/3.99  --bmc1_add_unsat_core                   none
% 27.02/3.99  --bmc1_unsat_core_children              false
% 27.02/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.02/3.99  --bmc1_out_stat                         full
% 27.02/3.99  --bmc1_ground_init                      false
% 27.02/3.99  --bmc1_pre_inst_next_state              false
% 27.02/3.99  --bmc1_pre_inst_state                   false
% 27.02/3.99  --bmc1_pre_inst_reach_state             false
% 27.02/3.99  --bmc1_out_unsat_core                   false
% 27.02/3.99  --bmc1_aig_witness_out                  false
% 27.02/3.99  --bmc1_verbose                          false
% 27.02/3.99  --bmc1_dump_clauses_tptp                false
% 27.02/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.02/3.99  --bmc1_dump_file                        -
% 27.02/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.02/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.02/3.99  --bmc1_ucm_extend_mode                  1
% 27.02/3.99  --bmc1_ucm_init_mode                    2
% 27.02/3.99  --bmc1_ucm_cone_mode                    none
% 27.02/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.02/3.99  --bmc1_ucm_relax_model                  4
% 27.02/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.02/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.02/3.99  --bmc1_ucm_layered_model                none
% 27.02/3.99  --bmc1_ucm_max_lemma_size               10
% 27.02/3.99  
% 27.02/3.99  ------ AIG Options
% 27.02/3.99  
% 27.02/3.99  --aig_mode                              false
% 27.02/3.99  
% 27.02/3.99  ------ Instantiation Options
% 27.02/3.99  
% 27.02/3.99  --instantiation_flag                    true
% 27.02/3.99  --inst_sos_flag                         false
% 27.02/3.99  --inst_sos_phase                        true
% 27.02/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.02/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.02/3.99  --inst_lit_sel_side                     num_symb
% 27.02/3.99  --inst_solver_per_active                1400
% 27.02/3.99  --inst_solver_calls_frac                1.
% 27.02/3.99  --inst_passive_queue_type               priority_queues
% 27.02/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.02/3.99  --inst_passive_queues_freq              [25;2]
% 27.02/3.99  --inst_dismatching                      true
% 27.02/3.99  --inst_eager_unprocessed_to_passive     true
% 27.02/3.99  --inst_prop_sim_given                   true
% 27.02/3.99  --inst_prop_sim_new                     false
% 27.02/3.99  --inst_subs_new                         false
% 27.02/3.99  --inst_eq_res_simp                      false
% 27.02/3.99  --inst_subs_given                       false
% 27.02/3.99  --inst_orphan_elimination               true
% 27.02/3.99  --inst_learning_loop_flag               true
% 27.02/3.99  --inst_learning_start                   3000
% 27.02/3.99  --inst_learning_factor                  2
% 27.02/3.99  --inst_start_prop_sim_after_learn       3
% 27.02/3.99  --inst_sel_renew                        solver
% 27.02/3.99  --inst_lit_activity_flag                true
% 27.02/3.99  --inst_restr_to_given                   false
% 27.02/3.99  --inst_activity_threshold               500
% 27.02/3.99  --inst_out_proof                        true
% 27.02/3.99  
% 27.02/3.99  ------ Resolution Options
% 27.02/3.99  
% 27.02/3.99  --resolution_flag                       true
% 27.02/3.99  --res_lit_sel                           adaptive
% 27.02/3.99  --res_lit_sel_side                      none
% 27.02/3.99  --res_ordering                          kbo
% 27.02/3.99  --res_to_prop_solver                    active
% 27.02/3.99  --res_prop_simpl_new                    false
% 27.02/3.99  --res_prop_simpl_given                  true
% 27.02/3.99  --res_passive_queue_type                priority_queues
% 27.02/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.02/3.99  --res_passive_queues_freq               [15;5]
% 27.02/3.99  --res_forward_subs                      full
% 27.02/3.99  --res_backward_subs                     full
% 27.02/3.99  --res_forward_subs_resolution           true
% 27.02/3.99  --res_backward_subs_resolution          true
% 27.02/3.99  --res_orphan_elimination                true
% 27.02/3.99  --res_time_limit                        2.
% 27.02/3.99  --res_out_proof                         true
% 27.02/3.99  
% 27.02/3.99  ------ Superposition Options
% 27.02/3.99  
% 27.02/3.99  --superposition_flag                    true
% 27.02/3.99  --sup_passive_queue_type                priority_queues
% 27.02/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.02/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.02/3.99  --demod_completeness_check              fast
% 27.02/3.99  --demod_use_ground                      true
% 27.02/3.99  --sup_to_prop_solver                    passive
% 27.02/3.99  --sup_prop_simpl_new                    true
% 27.02/3.99  --sup_prop_simpl_given                  true
% 27.02/3.99  --sup_fun_splitting                     false
% 27.02/3.99  --sup_smt_interval                      50000
% 27.02/3.99  
% 27.02/3.99  ------ Superposition Simplification Setup
% 27.02/3.99  
% 27.02/3.99  --sup_indices_passive                   []
% 27.02/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.02/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.02/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.02/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.02/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.02/3.99  --sup_full_bw                           [BwDemod]
% 27.02/3.99  --sup_immed_triv                        [TrivRules]
% 27.02/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.02/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.02/3.99  --sup_immed_bw_main                     []
% 27.02/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.02/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.02/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.02/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.02/3.99  
% 27.02/3.99  ------ Combination Options
% 27.02/3.99  
% 27.02/3.99  --comb_res_mult                         3
% 27.02/3.99  --comb_sup_mult                         2
% 27.02/3.99  --comb_inst_mult                        10
% 27.02/3.99  
% 27.02/3.99  ------ Debug Options
% 27.02/3.99  
% 27.02/3.99  --dbg_backtrace                         false
% 27.02/3.99  --dbg_dump_prop_clauses                 false
% 27.02/3.99  --dbg_dump_prop_clauses_file            -
% 27.02/3.99  --dbg_out_stat                          false
% 27.02/3.99  ------ Parsing...
% 27.02/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.02/3.99  
% 27.02/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 27.02/3.99  
% 27.02/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.02/3.99  
% 27.02/3.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.02/3.99  ------ Proving...
% 27.02/3.99  ------ Problem Properties 
% 27.02/3.99  
% 27.02/3.99  
% 27.02/3.99  clauses                                 4
% 27.02/3.99  conjectures                             1
% 27.02/3.99  EPR                                     0
% 27.02/3.99  Horn                                    4
% 27.02/3.99  unary                                   4
% 27.02/3.99  binary                                  0
% 27.02/3.99  lits                                    4
% 27.02/3.99  lits eq                                 4
% 27.02/3.99  fd_pure                                 0
% 27.02/3.99  fd_pseudo                               0
% 27.02/3.99  fd_cond                                 0
% 27.02/3.99  fd_pseudo_cond                          0
% 27.02/3.99  AC symbols                              0
% 27.02/3.99  
% 27.02/3.99  ------ Schedule UEQ
% 27.02/3.99  
% 27.02/3.99  ------ pure equality problem: resolution off 
% 27.02/3.99  
% 27.02/3.99  ------ Option_UEQ Time Limit: Unbounded
% 27.02/3.99  
% 27.02/3.99  
% 27.02/3.99  ------ 
% 27.02/3.99  Current options:
% 27.02/3.99  ------ 
% 27.02/3.99  
% 27.02/3.99  ------ Input Options
% 27.02/3.99  
% 27.02/3.99  --out_options                           all
% 27.02/3.99  --tptp_safe_out                         true
% 27.02/3.99  --problem_path                          ""
% 27.02/3.99  --include_path                          ""
% 27.02/3.99  --clausifier                            res/vclausify_rel
% 27.02/3.99  --clausifier_options                    --mode clausify
% 27.02/3.99  --stdin                                 false
% 27.02/3.99  --stats_out                             all
% 27.02/3.99  
% 27.02/3.99  ------ General Options
% 27.02/3.99  
% 27.02/3.99  --fof                                   false
% 27.02/3.99  --time_out_real                         305.
% 27.02/3.99  --time_out_virtual                      -1.
% 27.02/3.99  --symbol_type_check                     false
% 27.02/3.99  --clausify_out                          false
% 27.02/3.99  --sig_cnt_out                           false
% 27.02/3.99  --trig_cnt_out                          false
% 27.02/3.99  --trig_cnt_out_tolerance                1.
% 27.02/3.99  --trig_cnt_out_sk_spl                   false
% 27.02/3.99  --abstr_cl_out                          false
% 27.02/3.99  
% 27.02/3.99  ------ Global Options
% 27.02/3.99  
% 27.02/3.99  --schedule                              default
% 27.02/3.99  --add_important_lit                     false
% 27.02/3.99  --prop_solver_per_cl                    1000
% 27.02/3.99  --min_unsat_core                        false
% 27.02/3.99  --soft_assumptions                      false
% 27.02/3.99  --soft_lemma_size                       3
% 27.02/3.99  --prop_impl_unit_size                   0
% 27.02/3.99  --prop_impl_unit                        []
% 27.02/3.99  --share_sel_clauses                     true
% 27.02/3.99  --reset_solvers                         false
% 27.02/3.99  --bc_imp_inh                            [conj_cone]
% 27.02/3.99  --conj_cone_tolerance                   3.
% 27.02/3.99  --extra_neg_conj                        none
% 27.02/3.99  --large_theory_mode                     true
% 27.02/3.99  --prolific_symb_bound                   200
% 27.02/3.99  --lt_threshold                          2000
% 27.02/3.99  --clause_weak_htbl                      true
% 27.02/3.99  --gc_record_bc_elim                     false
% 27.02/3.99  
% 27.02/3.99  ------ Preprocessing Options
% 27.02/3.99  
% 27.02/3.99  --preprocessing_flag                    true
% 27.02/3.99  --time_out_prep_mult                    0.1
% 27.02/3.99  --splitting_mode                        input
% 27.02/3.99  --splitting_grd                         true
% 27.02/3.99  --splitting_cvd                         false
% 27.02/3.99  --splitting_cvd_svl                     false
% 27.02/3.99  --splitting_nvd                         32
% 27.02/3.99  --sub_typing                            true
% 27.02/3.99  --prep_gs_sim                           true
% 27.02/3.99  --prep_unflatten                        true
% 27.02/3.99  --prep_res_sim                          true
% 27.02/3.99  --prep_upred                            true
% 27.02/3.99  --prep_sem_filter                       exhaustive
% 27.02/3.99  --prep_sem_filter_out                   false
% 27.02/3.99  --pred_elim                             true
% 27.02/3.99  --res_sim_input                         true
% 27.02/3.99  --eq_ax_congr_red                       true
% 27.02/3.99  --pure_diseq_elim                       true
% 27.02/3.99  --brand_transform                       false
% 27.02/3.99  --non_eq_to_eq                          false
% 27.02/3.99  --prep_def_merge                        true
% 27.02/3.99  --prep_def_merge_prop_impl              false
% 27.02/3.99  --prep_def_merge_mbd                    true
% 27.02/3.99  --prep_def_merge_tr_red                 false
% 27.02/3.99  --prep_def_merge_tr_cl                  false
% 27.02/3.99  --smt_preprocessing                     true
% 27.02/3.99  --smt_ac_axioms                         fast
% 27.02/3.99  --preprocessed_out                      false
% 27.02/3.99  --preprocessed_stats                    false
% 27.02/3.99  
% 27.02/3.99  ------ Abstraction refinement Options
% 27.02/3.99  
% 27.02/3.99  --abstr_ref                             []
% 27.02/3.99  --abstr_ref_prep                        false
% 27.02/3.99  --abstr_ref_until_sat                   false
% 27.02/3.99  --abstr_ref_sig_restrict                funpre
% 27.02/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.02/3.99  --abstr_ref_under                       []
% 27.02/3.99  
% 27.02/3.99  ------ SAT Options
% 27.02/3.99  
% 27.02/3.99  --sat_mode                              false
% 27.02/3.99  --sat_fm_restart_options                ""
% 27.02/3.99  --sat_gr_def                            false
% 27.02/3.99  --sat_epr_types                         true
% 27.02/3.99  --sat_non_cyclic_types                  false
% 27.02/3.99  --sat_finite_models                     false
% 27.02/3.99  --sat_fm_lemmas                         false
% 27.02/3.99  --sat_fm_prep                           false
% 27.02/3.99  --sat_fm_uc_incr                        true
% 27.02/3.99  --sat_out_model                         small
% 27.02/3.99  --sat_out_clauses                       false
% 27.02/3.99  
% 27.02/3.99  ------ QBF Options
% 27.02/3.99  
% 27.02/3.99  --qbf_mode                              false
% 27.02/3.99  --qbf_elim_univ                         false
% 27.02/3.99  --qbf_dom_inst                          none
% 27.02/3.99  --qbf_dom_pre_inst                      false
% 27.02/3.99  --qbf_sk_in                             false
% 27.02/3.99  --qbf_pred_elim                         true
% 27.02/3.99  --qbf_split                             512
% 27.02/3.99  
% 27.02/3.99  ------ BMC1 Options
% 27.02/3.99  
% 27.02/3.99  --bmc1_incremental                      false
% 27.02/3.99  --bmc1_axioms                           reachable_all
% 27.02/3.99  --bmc1_min_bound                        0
% 27.02/3.99  --bmc1_max_bound                        -1
% 27.02/3.99  --bmc1_max_bound_default                -1
% 27.02/3.99  --bmc1_symbol_reachability              true
% 27.02/3.99  --bmc1_property_lemmas                  false
% 27.02/3.99  --bmc1_k_induction                      false
% 27.02/3.99  --bmc1_non_equiv_states                 false
% 27.02/3.99  --bmc1_deadlock                         false
% 27.02/3.99  --bmc1_ucm                              false
% 27.02/3.99  --bmc1_add_unsat_core                   none
% 27.02/3.99  --bmc1_unsat_core_children              false
% 27.02/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.02/3.99  --bmc1_out_stat                         full
% 27.02/3.99  --bmc1_ground_init                      false
% 27.02/3.99  --bmc1_pre_inst_next_state              false
% 27.02/3.99  --bmc1_pre_inst_state                   false
% 27.02/3.99  --bmc1_pre_inst_reach_state             false
% 27.02/3.99  --bmc1_out_unsat_core                   false
% 27.02/3.99  --bmc1_aig_witness_out                  false
% 27.02/3.99  --bmc1_verbose                          false
% 27.02/3.99  --bmc1_dump_clauses_tptp                false
% 27.02/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.02/3.99  --bmc1_dump_file                        -
% 27.02/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.02/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.02/3.99  --bmc1_ucm_extend_mode                  1
% 27.02/3.99  --bmc1_ucm_init_mode                    2
% 27.02/3.99  --bmc1_ucm_cone_mode                    none
% 27.02/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.02/3.99  --bmc1_ucm_relax_model                  4
% 27.02/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.02/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.02/3.99  --bmc1_ucm_layered_model                none
% 27.02/3.99  --bmc1_ucm_max_lemma_size               10
% 27.02/3.99  
% 27.02/3.99  ------ AIG Options
% 27.02/3.99  
% 27.02/3.99  --aig_mode                              false
% 27.02/3.99  
% 27.02/3.99  ------ Instantiation Options
% 27.02/3.99  
% 27.02/3.99  --instantiation_flag                    false
% 27.02/3.99  --inst_sos_flag                         false
% 27.02/3.99  --inst_sos_phase                        true
% 27.02/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.02/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.02/3.99  --inst_lit_sel_side                     num_symb
% 27.02/3.99  --inst_solver_per_active                1400
% 27.02/3.99  --inst_solver_calls_frac                1.
% 27.02/3.99  --inst_passive_queue_type               priority_queues
% 27.02/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.02/3.99  --inst_passive_queues_freq              [25;2]
% 27.02/3.99  --inst_dismatching                      true
% 27.02/3.99  --inst_eager_unprocessed_to_passive     true
% 27.02/3.99  --inst_prop_sim_given                   true
% 27.02/3.99  --inst_prop_sim_new                     false
% 27.02/3.99  --inst_subs_new                         false
% 27.02/3.99  --inst_eq_res_simp                      false
% 27.02/3.99  --inst_subs_given                       false
% 27.02/3.99  --inst_orphan_elimination               true
% 27.02/3.99  --inst_learning_loop_flag               true
% 27.02/3.99  --inst_learning_start                   3000
% 27.02/3.99  --inst_learning_factor                  2
% 27.02/3.99  --inst_start_prop_sim_after_learn       3
% 27.02/3.99  --inst_sel_renew                        solver
% 27.02/3.99  --inst_lit_activity_flag                true
% 27.02/3.99  --inst_restr_to_given                   false
% 27.02/3.99  --inst_activity_threshold               500
% 27.02/3.99  --inst_out_proof                        true
% 27.02/3.99  
% 27.02/3.99  ------ Resolution Options
% 27.02/3.99  
% 27.02/3.99  --resolution_flag                       false
% 27.02/3.99  --res_lit_sel                           adaptive
% 27.02/3.99  --res_lit_sel_side                      none
% 27.02/3.99  --res_ordering                          kbo
% 27.02/3.99  --res_to_prop_solver                    active
% 27.02/3.99  --res_prop_simpl_new                    false
% 27.02/3.99  --res_prop_simpl_given                  true
% 27.02/3.99  --res_passive_queue_type                priority_queues
% 27.02/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.02/3.99  --res_passive_queues_freq               [15;5]
% 27.02/3.99  --res_forward_subs                      full
% 27.02/3.99  --res_backward_subs                     full
% 27.02/3.99  --res_forward_subs_resolution           true
% 27.02/3.99  --res_backward_subs_resolution          true
% 27.02/3.99  --res_orphan_elimination                true
% 27.02/3.99  --res_time_limit                        2.
% 27.02/3.99  --res_out_proof                         true
% 27.02/3.99  
% 27.02/3.99  ------ Superposition Options
% 27.02/3.99  
% 27.02/3.99  --superposition_flag                    true
% 27.02/3.99  --sup_passive_queue_type                priority_queues
% 27.02/3.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.02/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.02/3.99  --demod_completeness_check              fast
% 27.02/3.99  --demod_use_ground                      true
% 27.02/3.99  --sup_to_prop_solver                    active
% 27.02/3.99  --sup_prop_simpl_new                    false
% 27.02/3.99  --sup_prop_simpl_given                  false
% 27.02/3.99  --sup_fun_splitting                     true
% 27.02/3.99  --sup_smt_interval                      10000
% 27.02/3.99  
% 27.02/3.99  ------ Superposition Simplification Setup
% 27.02/3.99  
% 27.02/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.02/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.02/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.02/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.02/3.99  --sup_full_triv                         [TrivRules]
% 27.02/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.02/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.02/3.99  --sup_immed_triv                        [TrivRules]
% 27.02/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.02/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.02/3.99  --sup_immed_bw_main                     []
% 27.02/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.02/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.02/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.02/3.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 27.02/3.99  
% 27.02/3.99  ------ Combination Options
% 27.02/3.99  
% 27.02/3.99  --comb_res_mult                         1
% 27.02/3.99  --comb_sup_mult                         1
% 27.02/3.99  --comb_inst_mult                        1000000
% 27.02/3.99  
% 27.02/3.99  ------ Debug Options
% 27.02/3.99  
% 27.02/3.99  --dbg_backtrace                         false
% 27.02/3.99  --dbg_dump_prop_clauses                 false
% 27.02/3.99  --dbg_dump_prop_clauses_file            -
% 27.02/3.99  --dbg_out_stat                          false
% 27.02/3.99  
% 27.02/3.99  
% 27.02/3.99  
% 27.02/3.99  
% 27.02/3.99  ------ Proving...
% 27.02/3.99  
% 27.02/3.99  
% 27.02/3.99  % SZS status Theorem for theBenchmark.p
% 27.02/3.99  
% 27.02/3.99   Resolution empty clause
% 27.02/3.99  
% 27.02/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.02/3.99  
% 27.02/3.99  fof(f1,axiom,(
% 27.02/3.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 27.02/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.02/3.99  
% 27.02/3.99  fof(f14,plain,(
% 27.02/3.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 27.02/3.99    inference(cnf_transformation,[],[f1])).
% 27.02/3.99  
% 27.02/3.99  fof(f7,axiom,(
% 27.02/3.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 27.02/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.02/3.99  
% 27.02/3.99  fof(f20,plain,(
% 27.02/3.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 27.02/3.99    inference(cnf_transformation,[],[f7])).
% 27.02/3.99  
% 27.02/3.99  fof(f6,axiom,(
% 27.02/3.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 27.02/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.02/3.99  
% 27.02/3.99  fof(f19,plain,(
% 27.02/3.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 27.02/3.99    inference(cnf_transformation,[],[f6])).
% 27.02/3.99  
% 27.02/3.99  fof(f5,axiom,(
% 27.02/3.99    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 27.02/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.02/3.99  
% 27.02/3.99  fof(f18,plain,(
% 27.02/3.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.02/3.99    inference(cnf_transformation,[],[f5])).
% 27.02/3.99  
% 27.02/3.99  fof(f4,axiom,(
% 27.02/3.99    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 27.02/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.02/3.99  
% 27.02/3.99  fof(f17,plain,(
% 27.02/3.99    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 27.02/3.99    inference(cnf_transformation,[],[f4])).
% 27.02/3.99  
% 27.02/3.99  fof(f24,plain,(
% 27.02/3.99    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))) = k2_enumset1(X0,X1,X2,X3)) )),
% 27.02/3.99    inference(definition_unfolding,[],[f18,f17])).
% 27.02/3.99  
% 27.02/3.99  fof(f26,plain,(
% 27.02/3.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 27.02/3.99    inference(definition_unfolding,[],[f19,f24])).
% 27.02/3.99  
% 27.02/3.99  fof(f27,plain,(
% 27.02/3.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k1_tarski(X4)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4))))) )),
% 27.02/3.99    inference(definition_unfolding,[],[f20,f24,f26])).
% 27.02/3.99  
% 27.02/3.99  fof(f8,axiom,(
% 27.02/3.99    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 27.02/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.02/3.99  
% 27.02/3.99  fof(f21,plain,(
% 27.02/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 27.02/3.99    inference(cnf_transformation,[],[f8])).
% 27.02/3.99  
% 27.02/3.99  fof(f2,axiom,(
% 27.02/3.99    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 27.02/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.02/3.99  
% 27.02/3.99  fof(f15,plain,(
% 27.02/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 27.02/3.99    inference(cnf_transformation,[],[f2])).
% 27.02/3.99  
% 27.02/3.99  fof(f23,plain,(
% 27.02/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 27.02/3.99    inference(definition_unfolding,[],[f15,f17,f17])).
% 27.02/3.99  
% 27.02/3.99  fof(f28,plain,(
% 27.02/3.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),k1_tarski(X5))) )),
% 27.02/3.99    inference(definition_unfolding,[],[f21,f26,f23])).
% 27.02/3.99  
% 27.02/3.99  fof(f9,conjecture,(
% 27.02/3.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 27.02/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.02/3.99  
% 27.02/3.99  fof(f10,negated_conjecture,(
% 27.02/3.99    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 27.02/3.99    inference(negated_conjecture,[],[f9])).
% 27.02/3.99  
% 27.02/3.99  fof(f11,plain,(
% 27.02/3.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 27.02/3.99    inference(ennf_transformation,[],[f10])).
% 27.02/3.99  
% 27.02/3.99  fof(f12,plain,(
% 27.02/3.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) => k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 27.02/3.99    introduced(choice_axiom,[])).
% 27.02/3.99  
% 27.02/3.99  fof(f13,plain,(
% 27.02/3.99    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 27.02/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f12])).
% 27.02/3.99  
% 27.02/3.99  fof(f22,plain,(
% 27.02/3.99    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 27.02/3.99    inference(cnf_transformation,[],[f13])).
% 27.02/3.99  
% 27.02/3.99  fof(f3,axiom,(
% 27.02/3.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 27.02/3.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.02/3.99  
% 27.02/3.99  fof(f16,plain,(
% 27.02/3.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 27.02/3.99    inference(cnf_transformation,[],[f3])).
% 27.02/3.99  
% 27.02/3.99  fof(f25,plain,(
% 27.02/3.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k2_xboole_0(k1_tarski(X4),k2_xboole_0(k2_tarski(X5,X6),k1_tarski(X7)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 27.02/3.99    inference(definition_unfolding,[],[f16,f24,f24])).
% 27.02/3.99  
% 27.02/3.99  fof(f29,plain,(
% 27.02/3.99    k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))),
% 27.02/3.99    inference(definition_unfolding,[],[f22,f23,f25])).
% 27.02/3.99  
% 27.02/3.99  cnf(c_0,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.02/3.99      inference(cnf_transformation,[],[f14]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_15,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(X0_39,X1_39),X2_39) = k2_xboole_0(X0_39,k2_xboole_0(X1_39,X2_39)) ),
% 27.02/3.99      inference(subtyping,[status(esa)],[c_0]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_1,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X3))),k1_tarski(X4)) ),
% 27.02/3.99      inference(cnf_transformation,[],[f27]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_14,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k1_tarski(X4_40)) ),
% 27.02/3.99      inference(subtyping,[status(esa)],[c_1]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_29,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_31,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_29]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_34,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40))),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_31,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_28,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k1_tarski(X4_40),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_14,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_39,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40))),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k1_tarski(X4_40),X0_39)) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_28,c_34]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_46,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40))),X0_39)) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_39,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_55,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_34,c_34,c_46]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_2,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_tarski(X2,X3),k1_tarski(X4)))),k1_tarski(X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)),k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) ),
% 27.02/3.99      inference(cnf_transformation,[],[f28]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_13,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),k1_tarski(X5_40)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
% 27.02/3.99      inference(subtyping,[status(esa)],[c_2]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_59,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40)))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_55,c_13]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_88,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40))))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_59]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_61,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39)) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_55,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_68,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_46]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_91,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39)) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_61,c_61,c_68]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_96,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39),X1_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))),X1_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_91,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_47,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k1_tarski(X4_40),X0_39)) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_46,c_39]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_73,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k1_tarski(X4_40),X0_39)) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_47,c_47,c_68]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_80,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))),X1_39) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40))),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_73,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_94,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k2_xboole_0(k1_tarski(X3_40),k1_tarski(X4_40)),X0_39))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_91]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_109,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))),X1_39) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39),X1_39)) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_96,c_80,c_94]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_104,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_68,c_68,c_94]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_106,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_104,c_55]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_242,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))),X1_39) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),k2_xboole_0(X0_39,X1_39)) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_106,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_245,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))),X1_39) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_242,c_106]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_348,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39),X1_39)) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_109,c_245]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_352,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39)),X1_39)) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_348]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_1065,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39),X1_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_352]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_2347,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),X0_39)),X1_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_1065]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_3189,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_2347]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_939,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),X0_39)))),X1_39) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_245]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_3578,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),X0_39)))),X1_39) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_3189,c_939]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_3599,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_3189]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_5655,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),X0_39)))),X1_39) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_3578,c_3578,c_3599]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_5659,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_xboole_0(k1_tarski(X5_40),k1_tarski(X6_40)),X0_39))))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_88,c_5655]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_36,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),k2_xboole_0(k1_tarski(X5_40),X0_39)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_13,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_140,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),k2_xboole_0(k1_tarski(X5_40),X0_39))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_36,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_100,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),X0_39)) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_94,c_91]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_141,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40)),X0_39)))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_140,c_73,c_100]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_142,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40)),X0_39)))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_141,c_94]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_369,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),k1_tarski(X6_40)) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_29,c_142]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_37,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40))),k1_tarski(X5_40))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_13,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_38,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))))) = k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_37,c_14]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_390,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),k1_tarski(X6_40)) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_369,c_38]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_1209,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40)))),k1_tarski(X6_40)) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_390]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_2557,plain,
% 27.02/3.99      ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),k1_tarski(X6_40))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_1209,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_2558,plain,
% 27.02/3.99      ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_2557,c_14]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_3395,plain,
% 27.02/3.99      ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_2558,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_1213,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40)),k1_tarski(X6_40))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_390,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_2576,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40)),k1_tarski(X6_40)),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_1213,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_3406,plain,
% 27.02/3.99      ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)),X0_39)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)))),X0_39) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_3395,c_106,c_2576]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_5805,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_xboole_0(k1_tarski(X5_40),k1_tarski(X6_40)),X0_39))))) = k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)),X0_39)))) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_5659,c_3406]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_89,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40))),X0_39)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_59,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_325,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40)),X0_39))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_89]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_647,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),k1_tarski(X5_40)),X0_39)))) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X0_40,X1_40),k1_tarski(X2_40)),k2_xboole_0(k2_tarski(X3_40,X4_40),k1_tarski(X5_40))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_325]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_5806,plain,
% 27.02/3.99      ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40)),X0_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40))),X0_39)) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_5805,c_647]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_40199,plain,
% 27.02/3.99      ( k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k1_tarski(X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40)))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_tarski(X4_40,X5_40),k1_tarski(X6_40))),k1_tarski(X7_40))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_29,c_5806]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_32,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),X0_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_29,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_48,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39)) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_32,c_34,c_46]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_51,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39),X1_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))),X1_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_48,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_60,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)))),k2_xboole_0(X0_39,X1_39)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))),X1_39) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_55,c_15]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_62,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39))),X1_39) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_60,c_55]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_197,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39),X1_39)) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_51,c_62]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_198,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k1_tarski(X4_40)),X0_39),X1_39)) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_197,c_104]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_201,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k1_tarski(X4_40),X0_39)),X1_39)) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_198]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_510,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_xboole_0(k2_tarski(X1_40,X2_40),k1_tarski(X3_40)),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_201]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_1460,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(X0_39,X1_39)))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_510]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_3574,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_3189,c_1460]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_4004,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k2_xboole_0(k1_tarski(X4_40),X0_39),X1_39)))) ),
% 27.02/3.99      inference(light_normalisation,[status(thm)],[c_3574,c_3574,c_3599]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_4010,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k2_tarski(X1_40,X2_40),k2_xboole_0(k1_tarski(X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(X0_39,X1_39))))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_4004]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_4831,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40)))))) = k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40))))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_2558,c_4010]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_40411,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(X0_40),k2_xboole_0(k1_tarski(X1_40),k2_xboole_0(k2_tarski(X2_40,X3_40),k2_xboole_0(k1_tarski(X4_40),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40)))))) = k2_xboole_0(k2_tarski(X0_40,X1_40),k2_xboole_0(k2_xboole_0(k2_tarski(X2_40,X3_40),k1_tarski(X4_40)),k2_xboole_0(k2_tarski(X5_40,X6_40),k1_tarski(X7_40)))) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_40199,c_38,c_390,c_4831]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_3,negated_conjecture,
% 27.02/3.99      ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) ),
% 27.02/3.99      inference(cnf_transformation,[],[f29]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_12,negated_conjecture,
% 27.02/3.99      ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) ),
% 27.02/3.99      inference(subtyping,[status(esa)],[c_3]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_24,plain,
% 27.02/3.99      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3))),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_15,c_12]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_25,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_24]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_105,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_104,c_25]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_131,plain,
% 27.02/3.99      ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_105]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_70249,plain,
% 27.02/3.99      ( k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_tarski(sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7))))) != k2_xboole_0(k2_tarski(sK0,sK1),k2_xboole_0(k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK4)),k2_xboole_0(k2_tarski(sK5,sK6),k1_tarski(sK7)))) ),
% 27.02/3.99      inference(demodulation,[status(thm)],[c_40411,c_131]) ).
% 27.02/3.99  
% 27.02/3.99  cnf(c_70685,plain,
% 27.02/3.99      ( $false ),
% 27.02/3.99      inference(superposition,[status(thm)],[c_15,c_70249]) ).
% 27.02/3.99  
% 27.02/3.99  
% 27.02/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.02/3.99  
% 27.02/3.99  ------                               Statistics
% 27.02/3.99  
% 27.02/3.99  ------ General
% 27.02/3.99  
% 27.02/3.99  abstr_ref_over_cycles:                  0
% 27.02/3.99  abstr_ref_under_cycles:                 0
% 27.02/3.99  gc_basic_clause_elim:                   0
% 27.02/3.99  forced_gc_time:                         0
% 27.02/3.99  parsing_time:                           0.011
% 27.02/3.99  unif_index_cands_time:                  0.
% 27.02/3.99  unif_index_add_time:                    0.
% 27.02/3.99  orderings_time:                         0.
% 27.02/3.99  out_proof_time:                         0.025
% 27.02/3.99  total_time:                             3.064
% 27.02/3.99  num_of_symbols:                         44
% 27.02/3.99  num_of_terms:                           58453
% 27.02/3.99  
% 27.02/3.99  ------ Preprocessing
% 27.02/3.99  
% 27.02/3.99  num_of_splits:                          0
% 27.02/3.99  num_of_split_atoms:                     0
% 27.02/3.99  num_of_reused_defs:                     0
% 27.02/3.99  num_eq_ax_congr_red:                    3
% 27.02/3.99  num_of_sem_filtered_clauses:            0
% 27.02/3.99  num_of_subtypes:                        2
% 27.02/3.99  monotx_restored_types:                  0
% 27.02/3.99  sat_num_of_epr_types:                   0
% 27.02/3.99  sat_num_of_non_cyclic_types:            0
% 27.02/3.99  sat_guarded_non_collapsed_types:        0
% 27.02/3.99  num_pure_diseq_elim:                    0
% 27.02/3.99  simp_replaced_by:                       0
% 27.02/3.99  res_preprocessed:                       11
% 27.02/3.99  prep_upred:                             0
% 27.02/3.99  prep_unflattend:                        0
% 27.02/3.99  smt_new_axioms:                         0
% 27.02/3.99  pred_elim_cands:                        0
% 27.02/3.99  pred_elim:                              0
% 27.02/3.99  pred_elim_cl:                           0
% 27.02/3.99  pred_elim_cycles:                       0
% 27.02/3.99  merged_defs:                            0
% 27.02/3.99  merged_defs_ncl:                        0
% 27.02/3.99  bin_hyper_res:                          0
% 27.02/3.99  prep_cycles:                            2
% 27.02/3.99  pred_elim_time:                         0.
% 27.02/3.99  splitting_time:                         0.
% 27.02/3.99  sem_filter_time:                        0.
% 27.02/3.99  monotx_time:                            0.
% 27.02/3.99  subtype_inf_time:                       0.
% 27.02/3.99  
% 27.02/3.99  ------ Problem properties
% 27.02/3.99  
% 27.02/3.99  clauses:                                4
% 27.02/3.99  conjectures:                            1
% 27.02/3.99  epr:                                    0
% 27.02/3.99  horn:                                   4
% 27.02/3.99  ground:                                 1
% 27.02/3.99  unary:                                  4
% 27.02/3.99  binary:                                 0
% 27.02/3.99  lits:                                   4
% 27.02/3.99  lits_eq:                                4
% 27.02/3.99  fd_pure:                                0
% 27.02/3.99  fd_pseudo:                              0
% 27.02/3.99  fd_cond:                                0
% 27.02/3.99  fd_pseudo_cond:                         0
% 27.02/3.99  ac_symbols:                             0
% 27.02/3.99  
% 27.02/3.99  ------ Propositional Solver
% 27.02/3.99  
% 27.02/3.99  prop_solver_calls:                      13
% 27.02/3.99  prop_fast_solver_calls:                 30
% 27.02/3.99  smt_solver_calls:                       0
% 27.02/3.99  smt_fast_solver_calls:                  0
% 27.02/3.99  prop_num_of_clauses:                    465
% 27.02/3.99  prop_preprocess_simplified:             135
% 27.02/3.99  prop_fo_subsumed:                       0
% 27.02/3.99  prop_solver_time:                       0.
% 27.02/3.99  smt_solver_time:                        0.
% 27.02/3.99  smt_fast_solver_time:                   0.
% 27.02/3.99  prop_fast_solver_time:                  0.
% 27.02/3.99  prop_unsat_core_time:                   0.
% 27.02/3.99  
% 27.02/3.99  ------ QBF
% 27.02/3.99  
% 27.02/3.99  qbf_q_res:                              0
% 27.02/3.99  qbf_num_tautologies:                    0
% 27.02/3.99  qbf_prep_cycles:                        0
% 27.02/3.99  
% 27.02/3.99  ------ BMC1
% 27.02/3.99  
% 27.02/3.99  bmc1_current_bound:                     -1
% 27.02/3.99  bmc1_last_solved_bound:                 -1
% 27.02/3.99  bmc1_unsat_core_size:                   -1
% 27.02/3.99  bmc1_unsat_core_parents_size:           -1
% 27.02/3.99  bmc1_merge_next_fun:                    0
% 27.02/3.99  bmc1_unsat_core_clauses_time:           0.
% 27.02/3.99  
% 27.02/3.99  ------ Instantiation
% 27.02/3.99  
% 27.02/3.99  inst_num_of_clauses:                    0
% 27.02/3.99  inst_num_in_passive:                    0
% 27.02/3.99  inst_num_in_active:                     0
% 27.02/3.99  inst_num_in_unprocessed:                0
% 27.02/3.99  inst_num_of_loops:                      0
% 27.02/3.99  inst_num_of_learning_restarts:          0
% 27.02/3.99  inst_num_moves_active_passive:          0
% 27.02/3.99  inst_lit_activity:                      0
% 27.02/3.99  inst_lit_activity_moves:                0
% 27.02/3.99  inst_num_tautologies:                   0
% 27.02/3.99  inst_num_prop_implied:                  0
% 27.02/3.99  inst_num_existing_simplified:           0
% 27.02/3.99  inst_num_eq_res_simplified:             0
% 27.02/3.99  inst_num_child_elim:                    0
% 27.02/3.99  inst_num_of_dismatching_blockings:      0
% 27.02/3.99  inst_num_of_non_proper_insts:           0
% 27.02/3.99  inst_num_of_duplicates:                 0
% 27.02/3.99  inst_inst_num_from_inst_to_res:         0
% 27.02/3.99  inst_dismatching_checking_time:         0.
% 27.02/3.99  
% 27.02/3.99  ------ Resolution
% 27.02/3.99  
% 27.02/3.99  res_num_of_clauses:                     0
% 27.02/3.99  res_num_in_passive:                     0
% 27.02/3.99  res_num_in_active:                      0
% 27.02/3.99  res_num_of_loops:                       13
% 27.02/3.99  res_forward_subset_subsumed:            0
% 27.02/3.99  res_backward_subset_subsumed:           0
% 27.02/3.99  res_forward_subsumed:                   0
% 27.02/3.99  res_backward_subsumed:                  0
% 27.02/3.99  res_forward_subsumption_resolution:     0
% 27.02/3.99  res_backward_subsumption_resolution:    0
% 27.02/3.99  res_clause_to_clause_subsumption:       10768
% 27.02/3.99  res_orphan_elimination:                 0
% 27.02/3.99  res_tautology_del:                      0
% 27.02/3.99  res_num_eq_res_simplified:              0
% 27.02/3.99  res_num_sel_changes:                    0
% 27.02/3.99  res_moves_from_active_to_pass:          0
% 27.02/3.99  
% 27.02/3.99  ------ Superposition
% 27.02/3.99  
% 27.02/3.99  sup_time_total:                         0.
% 27.02/3.99  sup_time_generating:                    0.
% 27.02/3.99  sup_time_sim_full:                      0.
% 27.02/3.99  sup_time_sim_immed:                     0.
% 27.02/3.99  
% 27.02/3.99  sup_num_of_clauses:                     1274
% 27.02/3.99  sup_num_in_active:                      159
% 27.02/3.99  sup_num_in_passive:                     1115
% 27.02/3.99  sup_num_of_loops:                       229
% 27.02/3.99  sup_fw_superposition:                   11439
% 27.02/3.99  sup_bw_superposition:                   6986
% 27.02/3.99  sup_immediate_simplified:               28085
% 27.02/3.99  sup_given_eliminated:                   13
% 27.02/3.99  comparisons_done:                       0
% 27.02/3.99  comparisons_avoided:                    0
% 27.02/3.99  
% 27.02/3.99  ------ Simplifications
% 27.02/3.99  
% 27.02/3.99  
% 27.02/3.99  sim_fw_subset_subsumed:                 0
% 27.02/3.99  sim_bw_subset_subsumed:                 0
% 27.02/3.99  sim_fw_subsumed:                        444
% 27.02/3.99  sim_bw_subsumed:                        10
% 27.02/3.99  sim_fw_subsumption_res:                 0
% 27.02/3.99  sim_bw_subsumption_res:                 0
% 27.02/3.99  sim_tautology_del:                      0
% 27.02/3.99  sim_eq_tautology_del:                   11099
% 27.02/3.99  sim_eq_res_simp:                        0
% 27.02/3.99  sim_fw_demodulated:                     45674
% 27.02/3.99  sim_bw_demodulated:                     246
% 27.02/3.99  sim_light_normalised:                   6096
% 27.02/3.99  sim_joinable_taut:                      0
% 27.02/3.99  sim_joinable_simp:                      0
% 27.02/3.99  sim_ac_normalised:                      0
% 27.02/3.99  sim_smt_subsumption:                    0
% 27.02/3.99  
%------------------------------------------------------------------------------
