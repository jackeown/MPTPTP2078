%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:41 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   32 (  80 expanded)
%              Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   33 (  81 expanded)
%              Number of equality atoms :   32 (  80 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :   11 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(ennf_transformation,[],[f11])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
   => k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).

fof(f24,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f18,f15])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))),k1_tarski(X0)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f22,f25,f28])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f23,f25,f29])).

fof(f32,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f24,f25,f26,f28,f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) ),
    inference(definition_unfolding,[],[f16,f25,f25,f25,f25])).

cnf(c_2,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_13,plain,
    ( k5_xboole_0(k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))),k5_xboole_0(X2_40,k3_xboole_0(X2_40,k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40)))))) = k5_xboole_0(X0_40,k5_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),k3_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),X0_40))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_28,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:07:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.39/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.39/0.99  
% 1.39/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.39/0.99  
% 1.39/0.99  ------  iProver source info
% 1.39/0.99  
% 1.39/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.39/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.39/0.99  git: non_committed_changes: false
% 1.39/0.99  git: last_make_outside_of_git: false
% 1.39/0.99  
% 1.39/0.99  ------ 
% 1.39/0.99  ------ Parsing...
% 1.39/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.39/0.99  
% 1.39/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.39/0.99  
% 1.39/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.39/0.99  
% 1.39/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.39/0.99  ------ Proving...
% 1.39/0.99  ------ Problem Properties 
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  clauses                                 3
% 1.39/0.99  conjectures                             1
% 1.39/0.99  EPR                                     0
% 1.39/0.99  Horn                                    3
% 1.39/0.99  unary                                   3
% 1.39/0.99  binary                                  0
% 1.39/0.99  lits                                    3
% 1.39/0.99  lits eq                                 3
% 1.39/0.99  fd_pure                                 0
% 1.39/0.99  fd_pseudo                               0
% 1.39/0.99  fd_cond                                 0
% 1.39/0.99  fd_pseudo_cond                          0
% 1.39/0.99  AC symbols                              0
% 1.39/0.99  
% 1.39/0.99  ------ Input Options Time Limit: Unbounded
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  ------ 
% 1.39/0.99  Current options:
% 1.39/0.99  ------ 
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  ------ Proving...
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  % SZS status Theorem for theBenchmark.p
% 1.39/0.99  
% 1.39/0.99   Resolution empty clause
% 1.39/0.99  
% 1.39/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.39/0.99  
% 1.39/0.99  fof(f10,conjecture,(
% 1.39/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 1.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f11,negated_conjecture,(
% 1.39/0.99    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 1.39/0.99    inference(negated_conjecture,[],[f10])).
% 1.39/0.99  
% 1.39/0.99  fof(f12,plain,(
% 1.39/0.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 1.39/0.99    inference(ennf_transformation,[],[f11])).
% 1.39/0.99  
% 1.39/0.99  fof(f13,plain,(
% 1.39/0.99    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) => k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 1.39/0.99    introduced(choice_axiom,[])).
% 1.39/0.99  
% 1.39/0.99  fof(f14,plain,(
% 1.39/0.99    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 1.39/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f12,f13])).
% 1.39/0.99  
% 1.39/0.99  fof(f24,plain,(
% 1.39/0.99    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 1.39/0.99    inference(cnf_transformation,[],[f14])).
% 1.39/0.99  
% 1.39/0.99  fof(f5,axiom,(
% 1.39/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 1.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f19,plain,(
% 1.39/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f5])).
% 1.39/0.99  
% 1.39/0.99  fof(f26,plain,(
% 1.39/0.99    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1)) )),
% 1.39/0.99    inference(definition_unfolding,[],[f19,f25])).
% 1.39/0.99  
% 1.39/0.99  fof(f9,axiom,(
% 1.39/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 1.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f23,plain,(
% 1.39/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f9])).
% 1.39/0.99  
% 1.39/0.99  fof(f8,axiom,(
% 1.39/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f22,plain,(
% 1.39/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f8])).
% 1.39/0.99  
% 1.39/0.99  fof(f7,axiom,(
% 1.39/0.99    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f21,plain,(
% 1.39/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f7])).
% 1.39/0.99  
% 1.39/0.99  fof(f4,axiom,(
% 1.39/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f18,plain,(
% 1.39/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f4])).
% 1.39/0.99  
% 1.39/0.99  fof(f1,axiom,(
% 1.39/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f15,plain,(
% 1.39/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/0.99    inference(cnf_transformation,[],[f1])).
% 1.39/0.99  
% 1.39/0.99  fof(f25,plain,(
% 1.39/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 1.39/0.99    inference(definition_unfolding,[],[f18,f15])).
% 1.39/0.99  
% 1.39/0.99  fof(f28,plain,(
% 1.39/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.39/0.99    inference(definition_unfolding,[],[f21,f25])).
% 1.39/0.99  
% 1.39/0.99  fof(f29,plain,(
% 1.39/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k1_tarski(X1)))),k1_tarski(X0)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.39/0.99    inference(definition_unfolding,[],[f22,f25,f28])).
% 1.39/0.99  
% 1.39/0.99  fof(f30,plain,(
% 1.39/0.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_tarski(X2)))),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_tarski(X2)))),k3_xboole_0(k5_xboole_0(k1_tarski(X2),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k1_tarski(X2)))),k1_tarski(X1)))),k1_tarski(X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 1.39/0.99    inference(definition_unfolding,[],[f23,f25,f29])).
% 1.39/0.99  
% 1.39/0.99  fof(f32,plain,(
% 1.39/0.99    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0))))),
% 1.39/0.99    inference(definition_unfolding,[],[f24,f25,f26,f28,f30])).
% 1.39/0.99  
% 1.39/0.99  fof(f2,axiom,(
% 1.39/0.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 1.39/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/0.99  
% 1.39/0.99  fof(f16,plain,(
% 1.39/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 1.39/0.99    inference(cnf_transformation,[],[f2])).
% 1.39/0.99  
% 1.39/0.99  fof(f31,plain,(
% 1.39/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))))) )),
% 1.39/0.99    inference(definition_unfolding,[],[f16,f25,f25,f25,f25])).
% 1.39/0.99  
% 1.39/0.99  cnf(c_2,negated_conjecture,
% 1.39/0.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))) ),
% 1.39/0.99      inference(cnf_transformation,[],[f32]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_11,negated_conjecture,
% 1.39/0.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k1_tarski(sK1)))),k1_tarski(sK0)))) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_0,plain,
% 1.39/0.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) ),
% 1.39/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_13,plain,
% 1.39/0.99      ( k5_xboole_0(k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))),k5_xboole_0(X2_40,k3_xboole_0(X2_40,k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40)))))) = k5_xboole_0(X0_40,k5_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),k3_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),X0_40))) ),
% 1.39/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 1.39/0.99  
% 1.39/0.99  cnf(c_28,plain,
% 1.39/0.99      ( $false ),
% 1.39/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_11,c_13]) ).
% 1.39/0.99  
% 1.39/0.99  
% 1.39/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.39/0.99  
% 1.39/0.99  ------                               Statistics
% 1.39/0.99  
% 1.39/0.99  ------ Selected
% 1.39/0.99  
% 1.39/0.99  total_time:                             0.042
% 1.39/0.99  
%------------------------------------------------------------------------------
