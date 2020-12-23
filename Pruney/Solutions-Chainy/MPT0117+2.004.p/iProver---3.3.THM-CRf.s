%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:05 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 305 expanded)
%              Number of clauses        :   35 (  84 expanded)
%              Number of leaves         :   11 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  104 ( 498 expanded)
%              Number of equality atoms :   57 ( 240 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f31,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f19,f33,f33])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) ),
    inference(definition_unfolding,[],[f29,f33,f23,f33,f23,f33,f23])).

fof(f30,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_274,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_277,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_552,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_274,c_277])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_943,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_552,c_0])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_955,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK1 ),
    inference(demodulation,[status(thm)],[c_943,c_6,c_7])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1261,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,sK1))))) = k5_xboole_0(k5_xboole_0(X0,sK2),k3_xboole_0(k5_xboole_0(X0,sK2),sK1)) ),
    inference(superposition,[status(thm)],[c_955,c_8])).

cnf(c_8714,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k5_xboole_0(sK2,sK2)))) = k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)) ),
    inference(superposition,[status(thm)],[c_552,c_1261])).

cnf(c_8758,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK2,sK2)))) = k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_8714,c_552,c_955])).

cnf(c_8759,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(demodulation,[status(thm)],[c_8758,c_7])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_273,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_553,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_273,c_277])).

cnf(c_8715,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k5_xboole_0(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
    inference(superposition,[status(thm)],[c_553,c_1261])).

cnf(c_1104,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_553,c_0])).

cnf(c_1116,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = sK1 ),
    inference(demodulation,[status(thm)],[c_1104,c_6,c_7])).

cnf(c_8754,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_8715,c_552,c_1116])).

cnf(c_8755,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_8754,c_7])).

cnf(c_8760,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) ),
    inference(demodulation,[status(thm)],[c_8759,c_8755])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_278,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9186,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) != k1_xboole_0
    | r1_tarski(k5_xboole_0(sK0,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8760,c_278])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3965,plain,
    ( ~ r1_tarski(X0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3967,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3965])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1313,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9186,c_3967,c_1313,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:06:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 3.81/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/1.00  
% 3.81/1.00  ------  iProver source info
% 3.81/1.00  
% 3.81/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.81/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/1.00  git: non_committed_changes: false
% 3.81/1.00  git: last_make_outside_of_git: false
% 3.81/1.00  
% 3.81/1.00  ------ 
% 3.81/1.00  ------ Parsing...
% 3.81/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/1.00  
% 3.81/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.00  ------ Proving...
% 3.81/1.00  ------ Problem Properties 
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  clauses                                 12
% 3.81/1.00  conjectures                             3
% 3.81/1.00  EPR                                     3
% 3.81/1.00  Horn                                    12
% 3.81/1.00  unary                                   9
% 3.81/1.00  binary                                  3
% 3.81/1.00  lits                                    15
% 3.81/1.00  lits eq                                 8
% 3.81/1.00  fd_pure                                 0
% 3.81/1.00  fd_pseudo                               0
% 3.81/1.00  fd_cond                                 0
% 3.81/1.00  fd_pseudo_cond                          0
% 3.81/1.00  AC symbols                              0
% 3.81/1.00  
% 3.81/1.00  ------ Input Options Time Limit: Unbounded
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ 
% 3.81/1.00  Current options:
% 3.81/1.00  ------ 
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  ------ Proving...
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  % SZS status Theorem for theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  fof(f11,conjecture,(
% 3.81/1.00    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f12,negated_conjecture,(
% 3.81/1.00    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 3.81/1.00    inference(negated_conjecture,[],[f11])).
% 3.81/1.00  
% 3.81/1.00  fof(f14,plain,(
% 3.81/1.00    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 3.81/1.00    inference(ennf_transformation,[],[f12])).
% 3.81/1.00  
% 3.81/1.00  fof(f15,plain,(
% 3.81/1.00    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 3.81/1.00    inference(flattening,[],[f14])).
% 3.81/1.00  
% 3.81/1.00  fof(f17,plain,(
% 3.81/1.00    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 3.81/1.00    introduced(choice_axiom,[])).
% 3.81/1.00  
% 3.81/1.00  fof(f18,plain,(
% 3.81/1.00    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 3.81/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 3.81/1.00  
% 3.81/1.00  fof(f31,plain,(
% 3.81/1.00    r1_tarski(sK2,sK1)),
% 3.81/1.00    inference(cnf_transformation,[],[f18])).
% 3.81/1.00  
% 3.81/1.00  fof(f5,axiom,(
% 3.81/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f13,plain,(
% 3.81/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.81/1.00    inference(ennf_transformation,[],[f5])).
% 3.81/1.00  
% 3.81/1.00  fof(f24,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f13])).
% 3.81/1.00  
% 3.81/1.00  fof(f1,axiom,(
% 3.81/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f19,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f1])).
% 3.81/1.00  
% 3.81/1.00  fof(f9,axiom,(
% 3.81/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f28,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.81/1.00    inference(cnf_transformation,[],[f9])).
% 3.81/1.00  
% 3.81/1.00  fof(f4,axiom,(
% 3.81/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f23,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.81/1.00    inference(cnf_transformation,[],[f4])).
% 3.81/1.00  
% 3.81/1.00  fof(f33,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.81/1.00    inference(definition_unfolding,[],[f28,f23])).
% 3.81/1.00  
% 3.81/1.00  fof(f34,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.81/1.00    inference(definition_unfolding,[],[f19,f33,f33])).
% 3.81/1.00  
% 3.81/1.00  fof(f7,axiom,(
% 3.81/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f26,plain,(
% 3.81/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.81/1.00    inference(cnf_transformation,[],[f7])).
% 3.81/1.00  
% 3.81/1.00  fof(f8,axiom,(
% 3.81/1.00    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f27,plain,(
% 3.81/1.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f8])).
% 3.81/1.00  
% 3.81/1.00  fof(f10,axiom,(
% 3.81/1.00    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f29,plain,(
% 3.81/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f10])).
% 3.81/1.00  
% 3.81/1.00  fof(f37,plain,(
% 3.81/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))))))) )),
% 3.81/1.00    inference(definition_unfolding,[],[f29,f33,f23,f33,f23,f33,f23])).
% 3.81/1.00  
% 3.81/1.00  fof(f30,plain,(
% 3.81/1.00    r1_tarski(sK0,sK1)),
% 3.81/1.00    inference(cnf_transformation,[],[f18])).
% 3.81/1.00  
% 3.81/1.00  fof(f3,axiom,(
% 3.81/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f16,plain,(
% 3.81/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.81/1.00    inference(nnf_transformation,[],[f3])).
% 3.81/1.00  
% 3.81/1.00  fof(f21,plain,(
% 3.81/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.81/1.00    inference(cnf_transformation,[],[f16])).
% 3.81/1.00  
% 3.81/1.00  fof(f36,plain,(
% 3.81/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.81/1.00    inference(definition_unfolding,[],[f21,f23])).
% 3.81/1.00  
% 3.81/1.00  fof(f22,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f16])).
% 3.81/1.00  
% 3.81/1.00  fof(f35,plain,(
% 3.81/1.00    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.81/1.00    inference(definition_unfolding,[],[f22,f23])).
% 3.81/1.00  
% 3.81/1.00  fof(f6,axiom,(
% 3.81/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.81/1.00  
% 3.81/1.00  fof(f25,plain,(
% 3.81/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.81/1.00    inference(cnf_transformation,[],[f6])).
% 3.81/1.00  
% 3.81/1.00  fof(f32,plain,(
% 3.81/1.00    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 3.81/1.00    inference(cnf_transformation,[],[f18])).
% 3.81/1.00  
% 3.81/1.00  cnf(c_10,negated_conjecture,
% 3.81/1.00      ( r1_tarski(sK2,sK1) ),
% 3.81/1.00      inference(cnf_transformation,[],[f31]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_274,plain,
% 3.81/1.00      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_4,plain,
% 3.81/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.81/1.00      inference(cnf_transformation,[],[f24]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_277,plain,
% 3.81/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_552,plain,
% 3.81/1.00      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_274,c_277]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_0,plain,
% 3.81/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.81/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_943,plain,
% 3.81/1.00      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,k5_xboole_0(sK2,sK2)) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_552,c_0]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_6,plain,
% 3.81/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.81/1.00      inference(cnf_transformation,[],[f26]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_7,plain,
% 3.81/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.81/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_955,plain,
% 3.81/1.00      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = sK1 ),
% 3.81/1.00      inference(demodulation,[status(thm)],[c_943,c_6,c_7]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_8,plain,
% 3.81/1.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))))),k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(k5_xboole_0(X0,X1),X2)) ),
% 3.81/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1261,plain,
% 3.81/1.00      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,sK1)),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X0))))),k5_xboole_0(X0,k3_xboole_0(X0,sK1))))) = k5_xboole_0(k5_xboole_0(X0,sK2),k3_xboole_0(k5_xboole_0(X0,sK2),sK1)) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_955,c_8]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_8714,plain,
% 3.81/1.00      ( k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),k5_xboole_0(sK2,sK2)))) = k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_552,c_1261]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_8758,plain,
% 3.81/1.00      ( k5_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK2,sK2)))) = k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),sK1)) ),
% 3.81/1.00      inference(light_normalisation,[status(thm)],[c_8714,c_552,c_955]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_8759,plain,
% 3.81/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 3.81/1.00      inference(demodulation,[status(thm)],[c_8758,c_7]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_11,negated_conjecture,
% 3.81/1.00      ( r1_tarski(sK0,sK1) ),
% 3.81/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_273,plain,
% 3.81/1.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_553,plain,
% 3.81/1.00      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_273,c_277]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_8715,plain,
% 3.81/1.00      ( k5_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k5_xboole_0(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_553,c_1261]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1104,plain,
% 3.81/1.00      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = k5_xboole_0(sK1,k5_xboole_0(sK0,sK0)) ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_553,c_0]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1116,plain,
% 3.81/1.00      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) = sK1 ),
% 3.81/1.00      inference(demodulation,[status(thm)],[c_1104,c_6,c_7]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_8754,plain,
% 3.81/1.00      ( k5_xboole_0(k5_xboole_0(sK0,sK0),k5_xboole_0(k5_xboole_0(sK2,sK2),k3_xboole_0(k5_xboole_0(sK2,sK2),k5_xboole_0(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) ),
% 3.81/1.00      inference(light_normalisation,[status(thm)],[c_8715,c_552,c_1116]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_8755,plain,
% 3.81/1.00      ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) ),
% 3.81/1.00      inference(demodulation,[status(thm)],[c_8754,c_7]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_8760,plain,
% 3.81/1.00      ( k5_xboole_0(k5_xboole_0(sK0,sK2),k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) ),
% 3.81/1.00      inference(demodulation,[status(thm)],[c_8759,c_8755]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_3,plain,
% 3.81/1.00      ( r1_tarski(X0,X1)
% 3.81/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.81/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_278,plain,
% 3.81/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 3.81/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_9186,plain,
% 3.81/1.00      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) != k1_xboole_0
% 3.81/1.00      | r1_tarski(k5_xboole_0(sK0,sK2),sK1) = iProver_top ),
% 3.81/1.00      inference(superposition,[status(thm)],[c_8760,c_278]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_2,plain,
% 3.81/1.00      ( ~ r1_tarski(X0,X1)
% 3.81/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.81/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_3965,plain,
% 3.81/1.00      ( ~ r1_tarski(X0,sK1)
% 3.81/1.00      | k5_xboole_0(X0,k3_xboole_0(X0,sK1)) = k1_xboole_0 ),
% 3.81/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_3967,plain,
% 3.81/1.00      ( ~ r1_tarski(k1_xboole_0,sK1)
% 3.81/1.00      | k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,sK1)) = k1_xboole_0 ),
% 3.81/1.00      inference(instantiation,[status(thm)],[c_3965]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_5,plain,
% 3.81/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.81/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_1313,plain,
% 3.81/1.00      ( r1_tarski(k1_xboole_0,sK1) ),
% 3.81/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_9,negated_conjecture,
% 3.81/1.00      ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
% 3.81/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(c_14,plain,
% 3.81/1.00      ( r1_tarski(k5_xboole_0(sK0,sK2),sK1) != iProver_top ),
% 3.81/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.81/1.00  
% 3.81/1.00  cnf(contradiction,plain,
% 3.81/1.00      ( $false ),
% 3.81/1.00      inference(minisat,[status(thm)],[c_9186,c_3967,c_1313,c_14]) ).
% 3.81/1.00  
% 3.81/1.00  
% 3.81/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/1.00  
% 3.81/1.00  ------                               Statistics
% 3.81/1.00  
% 3.81/1.00  ------ Selected
% 3.81/1.00  
% 3.81/1.00  total_time:                             0.468
% 3.81/1.00  
%------------------------------------------------------------------------------
