%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:50 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 343 expanded)
%              Number of clauses        :   50 ( 124 expanded)
%              Number of leaves         :   11 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  124 ( 509 expanded)
%              Number of equality atoms :   71 ( 281 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f27,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f27,f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f25,f20,f20])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f18,f20])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_575,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_652,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_0,c_575])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_577,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1488,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
    inference(superposition,[status(thm)],[c_652,c_577])).

cnf(c_7,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_576,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_917,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_576])).

cnf(c_1591,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_917])).

cnf(c_1957,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1591])).

cnf(c_2126,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_1957,c_577])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1586,plain,
    ( r1_tarski(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k3_xboole_0(X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_917])).

cnf(c_1608,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1586])).

cnf(c_1942,plain,
    ( r1_tarski(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1608])).

cnf(c_2210,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1942,c_577])).

cnf(c_3786,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = sK0 ),
    inference(superposition,[status(thm)],[c_0,c_2210])).

cnf(c_3816,plain,
    ( k3_xboole_0(sK0,sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3786,c_1488])).

cnf(c_807,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_0,c_7])).

cnf(c_5286,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_3816,c_807])).

cnf(c_6742,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_2126,c_5286])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_578,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1486,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_578,c_577])).

cnf(c_916,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_576])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_580,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3832,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_916,c_580])).

cnf(c_1490,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_916,c_577])).

cnf(c_3871,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3832,c_1490])).

cnf(c_1945,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK0),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_576])).

cnf(c_2124,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1945,c_577])).

cnf(c_3362,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_2124,c_0])).

cnf(c_4198,plain,
    ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3362,c_3871])).

cnf(c_6794,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6742,c_1486,c_3871,c_4198])).

cnf(c_8,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_119,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_120,plain,
    ( ~ r1_tarski(sK0,sK1)
    | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_119])).

cnf(c_574,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_120])).

cnf(c_812,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_574])).

cnf(c_1049,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK2,X1))) != sK0
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_812])).

cnf(c_1954,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1488,c_1049])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_590,plain,
    ( r1_tarski(sK0,sK1)
    | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_591,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
    | r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6794,c_1954,c_591])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:35:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.42/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.02  
% 3.42/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.42/1.02  
% 3.42/1.02  ------  iProver source info
% 3.42/1.02  
% 3.42/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.42/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.42/1.02  git: non_committed_changes: false
% 3.42/1.02  git: last_make_outside_of_git: false
% 3.42/1.02  
% 3.42/1.02  ------ 
% 3.42/1.02  
% 3.42/1.02  ------ Input Options
% 3.42/1.02  
% 3.42/1.02  --out_options                           all
% 3.42/1.02  --tptp_safe_out                         true
% 3.42/1.02  --problem_path                          ""
% 3.42/1.02  --include_path                          ""
% 3.42/1.02  --clausifier                            res/vclausify_rel
% 3.42/1.02  --clausifier_options                    ""
% 3.42/1.02  --stdin                                 false
% 3.42/1.02  --stats_out                             all
% 3.42/1.02  
% 3.42/1.02  ------ General Options
% 3.42/1.02  
% 3.42/1.02  --fof                                   false
% 3.42/1.02  --time_out_real                         305.
% 3.42/1.02  --time_out_virtual                      -1.
% 3.42/1.02  --symbol_type_check                     false
% 3.42/1.02  --clausify_out                          false
% 3.42/1.02  --sig_cnt_out                           false
% 3.42/1.02  --trig_cnt_out                          false
% 3.42/1.02  --trig_cnt_out_tolerance                1.
% 3.42/1.02  --trig_cnt_out_sk_spl                   false
% 3.42/1.02  --abstr_cl_out                          false
% 3.42/1.02  
% 3.42/1.02  ------ Global Options
% 3.42/1.02  
% 3.42/1.02  --schedule                              default
% 3.42/1.02  --add_important_lit                     false
% 3.42/1.02  --prop_solver_per_cl                    1000
% 3.42/1.02  --min_unsat_core                        false
% 3.42/1.02  --soft_assumptions                      false
% 3.42/1.02  --soft_lemma_size                       3
% 3.42/1.02  --prop_impl_unit_size                   0
% 3.42/1.02  --prop_impl_unit                        []
% 3.42/1.02  --share_sel_clauses                     true
% 3.42/1.02  --reset_solvers                         false
% 3.42/1.02  --bc_imp_inh                            [conj_cone]
% 3.42/1.02  --conj_cone_tolerance                   3.
% 3.42/1.02  --extra_neg_conj                        none
% 3.42/1.02  --large_theory_mode                     true
% 3.42/1.02  --prolific_symb_bound                   200
% 3.42/1.02  --lt_threshold                          2000
% 3.42/1.02  --clause_weak_htbl                      true
% 3.42/1.02  --gc_record_bc_elim                     false
% 3.42/1.02  
% 3.42/1.02  ------ Preprocessing Options
% 3.42/1.02  
% 3.42/1.02  --preprocessing_flag                    true
% 3.42/1.02  --time_out_prep_mult                    0.1
% 3.42/1.02  --splitting_mode                        input
% 3.42/1.02  --splitting_grd                         true
% 3.42/1.02  --splitting_cvd                         false
% 3.42/1.02  --splitting_cvd_svl                     false
% 3.42/1.02  --splitting_nvd                         32
% 3.42/1.02  --sub_typing                            true
% 3.42/1.02  --prep_gs_sim                           true
% 3.42/1.02  --prep_unflatten                        true
% 3.42/1.02  --prep_res_sim                          true
% 3.42/1.02  --prep_upred                            true
% 3.42/1.02  --prep_sem_filter                       exhaustive
% 3.42/1.02  --prep_sem_filter_out                   false
% 3.42/1.02  --pred_elim                             true
% 3.42/1.02  --res_sim_input                         true
% 3.42/1.02  --eq_ax_congr_red                       true
% 3.42/1.02  --pure_diseq_elim                       true
% 3.42/1.02  --brand_transform                       false
% 3.42/1.02  --non_eq_to_eq                          false
% 3.42/1.02  --prep_def_merge                        true
% 3.42/1.02  --prep_def_merge_prop_impl              false
% 3.42/1.02  --prep_def_merge_mbd                    true
% 3.42/1.02  --prep_def_merge_tr_red                 false
% 3.42/1.02  --prep_def_merge_tr_cl                  false
% 3.42/1.02  --smt_preprocessing                     true
% 3.42/1.02  --smt_ac_axioms                         fast
% 3.42/1.02  --preprocessed_out                      false
% 3.42/1.02  --preprocessed_stats                    false
% 3.42/1.02  
% 3.42/1.02  ------ Abstraction refinement Options
% 3.42/1.02  
% 3.42/1.02  --abstr_ref                             []
% 3.42/1.02  --abstr_ref_prep                        false
% 3.42/1.02  --abstr_ref_until_sat                   false
% 3.42/1.02  --abstr_ref_sig_restrict                funpre
% 3.42/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/1.02  --abstr_ref_under                       []
% 3.42/1.02  
% 3.42/1.02  ------ SAT Options
% 3.42/1.02  
% 3.42/1.02  --sat_mode                              false
% 3.42/1.02  --sat_fm_restart_options                ""
% 3.42/1.02  --sat_gr_def                            false
% 3.42/1.02  --sat_epr_types                         true
% 3.42/1.02  --sat_non_cyclic_types                  false
% 3.42/1.02  --sat_finite_models                     false
% 3.42/1.02  --sat_fm_lemmas                         false
% 3.42/1.02  --sat_fm_prep                           false
% 3.42/1.02  --sat_fm_uc_incr                        true
% 3.42/1.02  --sat_out_model                         small
% 3.42/1.02  --sat_out_clauses                       false
% 3.42/1.02  
% 3.42/1.02  ------ QBF Options
% 3.42/1.02  
% 3.42/1.02  --qbf_mode                              false
% 3.42/1.02  --qbf_elim_univ                         false
% 3.42/1.02  --qbf_dom_inst                          none
% 3.42/1.02  --qbf_dom_pre_inst                      false
% 3.42/1.02  --qbf_sk_in                             false
% 3.42/1.02  --qbf_pred_elim                         true
% 3.42/1.02  --qbf_split                             512
% 3.42/1.02  
% 3.42/1.02  ------ BMC1 Options
% 3.42/1.02  
% 3.42/1.02  --bmc1_incremental                      false
% 3.42/1.02  --bmc1_axioms                           reachable_all
% 3.42/1.02  --bmc1_min_bound                        0
% 3.42/1.02  --bmc1_max_bound                        -1
% 3.42/1.02  --bmc1_max_bound_default                -1
% 3.42/1.02  --bmc1_symbol_reachability              true
% 3.42/1.02  --bmc1_property_lemmas                  false
% 3.42/1.02  --bmc1_k_induction                      false
% 3.42/1.02  --bmc1_non_equiv_states                 false
% 3.42/1.02  --bmc1_deadlock                         false
% 3.42/1.02  --bmc1_ucm                              false
% 3.42/1.02  --bmc1_add_unsat_core                   none
% 3.42/1.02  --bmc1_unsat_core_children              false
% 3.42/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/1.02  --bmc1_out_stat                         full
% 3.42/1.02  --bmc1_ground_init                      false
% 3.42/1.02  --bmc1_pre_inst_next_state              false
% 3.42/1.02  --bmc1_pre_inst_state                   false
% 3.42/1.02  --bmc1_pre_inst_reach_state             false
% 3.42/1.02  --bmc1_out_unsat_core                   false
% 3.42/1.02  --bmc1_aig_witness_out                  false
% 3.42/1.02  --bmc1_verbose                          false
% 3.42/1.02  --bmc1_dump_clauses_tptp                false
% 3.42/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.42/1.02  --bmc1_dump_file                        -
% 3.42/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.42/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.42/1.02  --bmc1_ucm_extend_mode                  1
% 3.42/1.02  --bmc1_ucm_init_mode                    2
% 3.42/1.02  --bmc1_ucm_cone_mode                    none
% 3.42/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.42/1.02  --bmc1_ucm_relax_model                  4
% 3.42/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.42/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/1.02  --bmc1_ucm_layered_model                none
% 3.42/1.02  --bmc1_ucm_max_lemma_size               10
% 3.42/1.02  
% 3.42/1.02  ------ AIG Options
% 3.42/1.02  
% 3.42/1.02  --aig_mode                              false
% 3.42/1.02  
% 3.42/1.02  ------ Instantiation Options
% 3.42/1.02  
% 3.42/1.02  --instantiation_flag                    true
% 3.42/1.02  --inst_sos_flag                         true
% 3.42/1.02  --inst_sos_phase                        true
% 3.42/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/1.02  --inst_lit_sel_side                     num_symb
% 3.42/1.02  --inst_solver_per_active                1400
% 3.42/1.02  --inst_solver_calls_frac                1.
% 3.42/1.02  --inst_passive_queue_type               priority_queues
% 3.42/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/1.02  --inst_passive_queues_freq              [25;2]
% 3.42/1.02  --inst_dismatching                      true
% 3.42/1.02  --inst_eager_unprocessed_to_passive     true
% 3.42/1.02  --inst_prop_sim_given                   true
% 3.42/1.02  --inst_prop_sim_new                     false
% 3.42/1.02  --inst_subs_new                         false
% 3.42/1.02  --inst_eq_res_simp                      false
% 3.42/1.02  --inst_subs_given                       false
% 3.42/1.02  --inst_orphan_elimination               true
% 3.42/1.02  --inst_learning_loop_flag               true
% 3.42/1.02  --inst_learning_start                   3000
% 3.42/1.02  --inst_learning_factor                  2
% 3.42/1.02  --inst_start_prop_sim_after_learn       3
% 3.42/1.02  --inst_sel_renew                        solver
% 3.42/1.02  --inst_lit_activity_flag                true
% 3.42/1.02  --inst_restr_to_given                   false
% 3.42/1.02  --inst_activity_threshold               500
% 3.42/1.02  --inst_out_proof                        true
% 3.42/1.02  
% 3.42/1.02  ------ Resolution Options
% 3.42/1.02  
% 3.42/1.02  --resolution_flag                       true
% 3.42/1.02  --res_lit_sel                           adaptive
% 3.42/1.02  --res_lit_sel_side                      none
% 3.42/1.02  --res_ordering                          kbo
% 3.42/1.02  --res_to_prop_solver                    active
% 3.42/1.02  --res_prop_simpl_new                    false
% 3.42/1.02  --res_prop_simpl_given                  true
% 3.42/1.02  --res_passive_queue_type                priority_queues
% 3.42/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/1.02  --res_passive_queues_freq               [15;5]
% 3.42/1.02  --res_forward_subs                      full
% 3.42/1.02  --res_backward_subs                     full
% 3.42/1.02  --res_forward_subs_resolution           true
% 3.42/1.02  --res_backward_subs_resolution          true
% 3.42/1.02  --res_orphan_elimination                true
% 3.42/1.02  --res_time_limit                        2.
% 3.42/1.02  --res_out_proof                         true
% 3.42/1.02  
% 3.42/1.02  ------ Superposition Options
% 3.42/1.02  
% 3.42/1.02  --superposition_flag                    true
% 3.42/1.02  --sup_passive_queue_type                priority_queues
% 3.42/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.42/1.02  --demod_completeness_check              fast
% 3.42/1.02  --demod_use_ground                      true
% 3.42/1.02  --sup_to_prop_solver                    passive
% 3.42/1.02  --sup_prop_simpl_new                    true
% 3.42/1.02  --sup_prop_simpl_given                  true
% 3.42/1.02  --sup_fun_splitting                     true
% 3.42/1.02  --sup_smt_interval                      50000
% 3.42/1.02  
% 3.42/1.02  ------ Superposition Simplification Setup
% 3.42/1.02  
% 3.42/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.42/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.42/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.42/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.42/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.42/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.42/1.02  --sup_immed_triv                        [TrivRules]
% 3.42/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.02  --sup_immed_bw_main                     []
% 3.42/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.42/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.02  --sup_input_bw                          []
% 3.42/1.02  
% 3.42/1.02  ------ Combination Options
% 3.42/1.02  
% 3.42/1.02  --comb_res_mult                         3
% 3.42/1.02  --comb_sup_mult                         2
% 3.42/1.02  --comb_inst_mult                        10
% 3.42/1.02  
% 3.42/1.02  ------ Debug Options
% 3.42/1.02  
% 3.42/1.02  --dbg_backtrace                         false
% 3.42/1.02  --dbg_dump_prop_clauses                 false
% 3.42/1.02  --dbg_dump_prop_clauses_file            -
% 3.42/1.02  --dbg_out_stat                          false
% 3.42/1.02  ------ Parsing...
% 3.42/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.42/1.02  
% 3.42/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.42/1.02  
% 3.42/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.42/1.02  
% 3.42/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.42/1.02  ------ Proving...
% 3.42/1.02  ------ Problem Properties 
% 3.42/1.02  
% 3.42/1.02  
% 3.42/1.02  clauses                                 10
% 3.42/1.02  conjectures                             1
% 3.42/1.02  EPR                                     0
% 3.42/1.02  Horn                                    10
% 3.42/1.02  unary                                   6
% 3.42/1.02  binary                                  4
% 3.42/1.02  lits                                    14
% 3.42/1.02  lits eq                                 7
% 3.42/1.02  fd_pure                                 0
% 3.42/1.02  fd_pseudo                               0
% 3.42/1.02  fd_cond                                 0
% 3.42/1.02  fd_pseudo_cond                          0
% 3.42/1.02  AC symbols                              0
% 3.42/1.02  
% 3.42/1.02  ------ Schedule dynamic 5 is on 
% 3.42/1.02  
% 3.42/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.42/1.02  
% 3.42/1.02  
% 3.42/1.02  ------ 
% 3.42/1.02  Current options:
% 3.42/1.02  ------ 
% 3.42/1.02  
% 3.42/1.02  ------ Input Options
% 3.42/1.02  
% 3.42/1.02  --out_options                           all
% 3.42/1.02  --tptp_safe_out                         true
% 3.42/1.02  --problem_path                          ""
% 3.42/1.02  --include_path                          ""
% 3.42/1.02  --clausifier                            res/vclausify_rel
% 3.42/1.02  --clausifier_options                    ""
% 3.42/1.02  --stdin                                 false
% 3.42/1.02  --stats_out                             all
% 3.42/1.02  
% 3.42/1.02  ------ General Options
% 3.42/1.02  
% 3.42/1.02  --fof                                   false
% 3.42/1.02  --time_out_real                         305.
% 3.42/1.02  --time_out_virtual                      -1.
% 3.42/1.02  --symbol_type_check                     false
% 3.42/1.02  --clausify_out                          false
% 3.42/1.02  --sig_cnt_out                           false
% 3.42/1.02  --trig_cnt_out                          false
% 3.42/1.02  --trig_cnt_out_tolerance                1.
% 3.42/1.02  --trig_cnt_out_sk_spl                   false
% 3.42/1.02  --abstr_cl_out                          false
% 3.42/1.02  
% 3.42/1.02  ------ Global Options
% 3.42/1.02  
% 3.42/1.02  --schedule                              default
% 3.42/1.02  --add_important_lit                     false
% 3.42/1.02  --prop_solver_per_cl                    1000
% 3.42/1.02  --min_unsat_core                        false
% 3.42/1.02  --soft_assumptions                      false
% 3.42/1.02  --soft_lemma_size                       3
% 3.42/1.02  --prop_impl_unit_size                   0
% 3.42/1.02  --prop_impl_unit                        []
% 3.42/1.02  --share_sel_clauses                     true
% 3.42/1.02  --reset_solvers                         false
% 3.42/1.02  --bc_imp_inh                            [conj_cone]
% 3.42/1.02  --conj_cone_tolerance                   3.
% 3.42/1.02  --extra_neg_conj                        none
% 3.42/1.02  --large_theory_mode                     true
% 3.42/1.02  --prolific_symb_bound                   200
% 3.42/1.02  --lt_threshold                          2000
% 3.42/1.02  --clause_weak_htbl                      true
% 3.42/1.02  --gc_record_bc_elim                     false
% 3.42/1.02  
% 3.42/1.02  ------ Preprocessing Options
% 3.42/1.02  
% 3.42/1.02  --preprocessing_flag                    true
% 3.42/1.02  --time_out_prep_mult                    0.1
% 3.42/1.02  --splitting_mode                        input
% 3.42/1.02  --splitting_grd                         true
% 3.42/1.02  --splitting_cvd                         false
% 3.42/1.02  --splitting_cvd_svl                     false
% 3.42/1.02  --splitting_nvd                         32
% 3.42/1.02  --sub_typing                            true
% 3.42/1.02  --prep_gs_sim                           true
% 3.42/1.02  --prep_unflatten                        true
% 3.42/1.02  --prep_res_sim                          true
% 3.42/1.02  --prep_upred                            true
% 3.42/1.02  --prep_sem_filter                       exhaustive
% 3.42/1.02  --prep_sem_filter_out                   false
% 3.42/1.02  --pred_elim                             true
% 3.42/1.02  --res_sim_input                         true
% 3.42/1.02  --eq_ax_congr_red                       true
% 3.42/1.02  --pure_diseq_elim                       true
% 3.42/1.02  --brand_transform                       false
% 3.42/1.02  --non_eq_to_eq                          false
% 3.42/1.02  --prep_def_merge                        true
% 3.42/1.02  --prep_def_merge_prop_impl              false
% 3.42/1.02  --prep_def_merge_mbd                    true
% 3.42/1.02  --prep_def_merge_tr_red                 false
% 3.42/1.02  --prep_def_merge_tr_cl                  false
% 3.42/1.02  --smt_preprocessing                     true
% 3.42/1.02  --smt_ac_axioms                         fast
% 3.42/1.02  --preprocessed_out                      false
% 3.42/1.02  --preprocessed_stats                    false
% 3.42/1.02  
% 3.42/1.02  ------ Abstraction refinement Options
% 3.42/1.02  
% 3.42/1.02  --abstr_ref                             []
% 3.42/1.02  --abstr_ref_prep                        false
% 3.42/1.02  --abstr_ref_until_sat                   false
% 3.42/1.02  --abstr_ref_sig_restrict                funpre
% 3.42/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.42/1.02  --abstr_ref_under                       []
% 3.42/1.02  
% 3.42/1.02  ------ SAT Options
% 3.42/1.02  
% 3.42/1.02  --sat_mode                              false
% 3.42/1.02  --sat_fm_restart_options                ""
% 3.42/1.02  --sat_gr_def                            false
% 3.42/1.02  --sat_epr_types                         true
% 3.42/1.02  --sat_non_cyclic_types                  false
% 3.42/1.02  --sat_finite_models                     false
% 3.42/1.02  --sat_fm_lemmas                         false
% 3.42/1.02  --sat_fm_prep                           false
% 3.42/1.02  --sat_fm_uc_incr                        true
% 3.42/1.02  --sat_out_model                         small
% 3.42/1.02  --sat_out_clauses                       false
% 3.42/1.02  
% 3.42/1.02  ------ QBF Options
% 3.42/1.02  
% 3.42/1.02  --qbf_mode                              false
% 3.42/1.02  --qbf_elim_univ                         false
% 3.42/1.02  --qbf_dom_inst                          none
% 3.42/1.02  --qbf_dom_pre_inst                      false
% 3.42/1.02  --qbf_sk_in                             false
% 3.42/1.02  --qbf_pred_elim                         true
% 3.42/1.02  --qbf_split                             512
% 3.42/1.02  
% 3.42/1.02  ------ BMC1 Options
% 3.42/1.02  
% 3.42/1.02  --bmc1_incremental                      false
% 3.42/1.02  --bmc1_axioms                           reachable_all
% 3.42/1.02  --bmc1_min_bound                        0
% 3.42/1.02  --bmc1_max_bound                        -1
% 3.42/1.02  --bmc1_max_bound_default                -1
% 3.42/1.02  --bmc1_symbol_reachability              true
% 3.42/1.02  --bmc1_property_lemmas                  false
% 3.42/1.02  --bmc1_k_induction                      false
% 3.42/1.02  --bmc1_non_equiv_states                 false
% 3.42/1.02  --bmc1_deadlock                         false
% 3.42/1.02  --bmc1_ucm                              false
% 3.42/1.02  --bmc1_add_unsat_core                   none
% 3.42/1.02  --bmc1_unsat_core_children              false
% 3.42/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.42/1.02  --bmc1_out_stat                         full
% 3.42/1.02  --bmc1_ground_init                      false
% 3.42/1.02  --bmc1_pre_inst_next_state              false
% 3.42/1.02  --bmc1_pre_inst_state                   false
% 3.42/1.02  --bmc1_pre_inst_reach_state             false
% 3.42/1.02  --bmc1_out_unsat_core                   false
% 3.42/1.02  --bmc1_aig_witness_out                  false
% 3.42/1.02  --bmc1_verbose                          false
% 3.42/1.02  --bmc1_dump_clauses_tptp                false
% 3.42/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.42/1.02  --bmc1_dump_file                        -
% 3.42/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.42/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.42/1.02  --bmc1_ucm_extend_mode                  1
% 3.42/1.02  --bmc1_ucm_init_mode                    2
% 3.42/1.02  --bmc1_ucm_cone_mode                    none
% 3.42/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.42/1.02  --bmc1_ucm_relax_model                  4
% 3.42/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.42/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.42/1.02  --bmc1_ucm_layered_model                none
% 3.42/1.02  --bmc1_ucm_max_lemma_size               10
% 3.42/1.02  
% 3.42/1.02  ------ AIG Options
% 3.42/1.02  
% 3.42/1.02  --aig_mode                              false
% 3.42/1.02  
% 3.42/1.02  ------ Instantiation Options
% 3.42/1.02  
% 3.42/1.02  --instantiation_flag                    true
% 3.42/1.02  --inst_sos_flag                         true
% 3.42/1.02  --inst_sos_phase                        true
% 3.42/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.42/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.42/1.02  --inst_lit_sel_side                     none
% 3.42/1.02  --inst_solver_per_active                1400
% 3.42/1.02  --inst_solver_calls_frac                1.
% 3.42/1.02  --inst_passive_queue_type               priority_queues
% 3.42/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.42/1.02  --inst_passive_queues_freq              [25;2]
% 3.42/1.02  --inst_dismatching                      true
% 3.42/1.02  --inst_eager_unprocessed_to_passive     true
% 3.42/1.02  --inst_prop_sim_given                   true
% 3.42/1.02  --inst_prop_sim_new                     false
% 3.42/1.02  --inst_subs_new                         false
% 3.42/1.02  --inst_eq_res_simp                      false
% 3.42/1.02  --inst_subs_given                       false
% 3.42/1.02  --inst_orphan_elimination               true
% 3.42/1.02  --inst_learning_loop_flag               true
% 3.42/1.02  --inst_learning_start                   3000
% 3.42/1.02  --inst_learning_factor                  2
% 3.42/1.02  --inst_start_prop_sim_after_learn       3
% 3.42/1.02  --inst_sel_renew                        solver
% 3.42/1.02  --inst_lit_activity_flag                true
% 3.42/1.02  --inst_restr_to_given                   false
% 3.42/1.02  --inst_activity_threshold               500
% 3.42/1.02  --inst_out_proof                        true
% 3.42/1.02  
% 3.42/1.02  ------ Resolution Options
% 3.42/1.02  
% 3.42/1.02  --resolution_flag                       false
% 3.42/1.02  --res_lit_sel                           adaptive
% 3.42/1.02  --res_lit_sel_side                      none
% 3.42/1.02  --res_ordering                          kbo
% 3.42/1.02  --res_to_prop_solver                    active
% 3.42/1.02  --res_prop_simpl_new                    false
% 3.42/1.02  --res_prop_simpl_given                  true
% 3.42/1.02  --res_passive_queue_type                priority_queues
% 3.42/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.42/1.02  --res_passive_queues_freq               [15;5]
% 3.42/1.02  --res_forward_subs                      full
% 3.42/1.02  --res_backward_subs                     full
% 3.42/1.02  --res_forward_subs_resolution           true
% 3.42/1.02  --res_backward_subs_resolution          true
% 3.42/1.02  --res_orphan_elimination                true
% 3.42/1.02  --res_time_limit                        2.
% 3.42/1.02  --res_out_proof                         true
% 3.42/1.02  
% 3.42/1.02  ------ Superposition Options
% 3.42/1.02  
% 3.42/1.02  --superposition_flag                    true
% 3.42/1.02  --sup_passive_queue_type                priority_queues
% 3.42/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.42/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.42/1.02  --demod_completeness_check              fast
% 3.42/1.02  --demod_use_ground                      true
% 3.42/1.02  --sup_to_prop_solver                    passive
% 3.42/1.02  --sup_prop_simpl_new                    true
% 3.42/1.02  --sup_prop_simpl_given                  true
% 3.42/1.02  --sup_fun_splitting                     true
% 3.42/1.02  --sup_smt_interval                      50000
% 3.42/1.02  
% 3.42/1.02  ------ Superposition Simplification Setup
% 3.42/1.02  
% 3.42/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.42/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.42/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.42/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.42/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.42/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.42/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.42/1.02  --sup_immed_triv                        [TrivRules]
% 3.42/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.02  --sup_immed_bw_main                     []
% 3.42/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.42/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.42/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.42/1.02  --sup_input_bw                          []
% 3.42/1.02  
% 3.42/1.02  ------ Combination Options
% 3.42/1.02  
% 3.42/1.02  --comb_res_mult                         3
% 3.42/1.02  --comb_sup_mult                         2
% 3.42/1.02  --comb_inst_mult                        10
% 3.42/1.02  
% 3.42/1.02  ------ Debug Options
% 3.42/1.02  
% 3.42/1.02  --dbg_backtrace                         false
% 3.42/1.02  --dbg_dump_prop_clauses                 false
% 3.42/1.02  --dbg_dump_prop_clauses_file            -
% 3.42/1.02  --dbg_out_stat                          false
% 3.42/1.02  
% 3.42/1.02  
% 3.42/1.02  
% 3.42/1.02  
% 3.42/1.02  ------ Proving...
% 3.42/1.02  
% 3.42/1.02  
% 3.42/1.02  % SZS status Theorem for theBenchmark.p
% 3.42/1.02  
% 3.42/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.42/1.02  
% 3.42/1.02  fof(f1,axiom,(
% 3.42/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f17,plain,(
% 3.42/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.42/1.02    inference(cnf_transformation,[],[f1])).
% 3.42/1.02  
% 3.42/1.02  fof(f10,conjecture,(
% 3.42/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f11,negated_conjecture,(
% 3.42/1.02    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.42/1.02    inference(negated_conjecture,[],[f10])).
% 3.42/1.02  
% 3.42/1.02  fof(f13,plain,(
% 3.42/1.02    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.42/1.02    inference(ennf_transformation,[],[f11])).
% 3.42/1.02  
% 3.42/1.02  fof(f15,plain,(
% 3.42/1.02    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 3.42/1.02    introduced(choice_axiom,[])).
% 3.42/1.02  
% 3.42/1.02  fof(f16,plain,(
% 3.42/1.02    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.42/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 3.42/1.02  
% 3.42/1.02  fof(f27,plain,(
% 3.42/1.02    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 3.42/1.02    inference(cnf_transformation,[],[f16])).
% 3.42/1.02  
% 3.42/1.02  fof(f3,axiom,(
% 3.42/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f20,plain,(
% 3.42/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.42/1.02    inference(cnf_transformation,[],[f3])).
% 3.42/1.02  
% 3.42/1.02  fof(f35,plain,(
% 3.42/1.02    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 3.42/1.02    inference(definition_unfolding,[],[f27,f20])).
% 3.42/1.02  
% 3.42/1.02  fof(f5,axiom,(
% 3.42/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f12,plain,(
% 3.42/1.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.42/1.02    inference(ennf_transformation,[],[f5])).
% 3.42/1.02  
% 3.42/1.02  fof(f22,plain,(
% 3.42/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.42/1.02    inference(cnf_transformation,[],[f12])).
% 3.42/1.02  
% 3.42/1.02  fof(f8,axiom,(
% 3.42/1.02    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f25,plain,(
% 3.42/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.42/1.02    inference(cnf_transformation,[],[f8])).
% 3.42/1.02  
% 3.42/1.02  fof(f33,plain,(
% 3.42/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 3.42/1.02    inference(definition_unfolding,[],[f25,f20,f20])).
% 3.42/1.02  
% 3.42/1.02  fof(f6,axiom,(
% 3.42/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f23,plain,(
% 3.42/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.42/1.02    inference(cnf_transformation,[],[f6])).
% 3.42/1.02  
% 3.42/1.02  fof(f31,plain,(
% 3.42/1.02    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 3.42/1.02    inference(definition_unfolding,[],[f23,f20])).
% 3.42/1.02  
% 3.42/1.02  fof(f7,axiom,(
% 3.42/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f24,plain,(
% 3.42/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.42/1.02    inference(cnf_transformation,[],[f7])).
% 3.42/1.02  
% 3.42/1.02  fof(f32,plain,(
% 3.42/1.02    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 3.42/1.02    inference(definition_unfolding,[],[f24,f20])).
% 3.42/1.02  
% 3.42/1.02  fof(f4,axiom,(
% 3.42/1.02    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f21,plain,(
% 3.42/1.02    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.42/1.02    inference(cnf_transformation,[],[f4])).
% 3.42/1.02  
% 3.42/1.02  fof(f2,axiom,(
% 3.42/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f14,plain,(
% 3.42/1.02    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.42/1.02    inference(nnf_transformation,[],[f2])).
% 3.42/1.02  
% 3.42/1.02  fof(f19,plain,(
% 3.42/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.42/1.02    inference(cnf_transformation,[],[f14])).
% 3.42/1.02  
% 3.42/1.02  fof(f29,plain,(
% 3.42/1.02    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.42/1.02    inference(definition_unfolding,[],[f19,f20])).
% 3.42/1.02  
% 3.42/1.02  fof(f9,axiom,(
% 3.42/1.02    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.42/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.42/1.02  
% 3.42/1.02  fof(f26,plain,(
% 3.42/1.02    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.42/1.02    inference(cnf_transformation,[],[f9])).
% 3.42/1.02  
% 3.42/1.02  fof(f34,plain,(
% 3.42/1.02    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 3.42/1.02    inference(definition_unfolding,[],[f26,f20])).
% 3.42/1.02  
% 3.42/1.02  fof(f28,plain,(
% 3.42/1.02    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 3.42/1.02    inference(cnf_transformation,[],[f16])).
% 3.42/1.02  
% 3.42/1.02  fof(f18,plain,(
% 3.42/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.42/1.02    inference(cnf_transformation,[],[f14])).
% 3.42/1.02  
% 3.42/1.02  fof(f30,plain,(
% 3.42/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.42/1.02    inference(definition_unfolding,[],[f18,f20])).
% 3.42/1.02  
% 3.42/1.02  cnf(c_0,plain,
% 3.42/1.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.42/1.02      inference(cnf_transformation,[],[f17]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_10,negated_conjecture,
% 3.42/1.02      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
% 3.42/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_575,plain,
% 3.42/1.02      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = iProver_top ),
% 3.42/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_652,plain,
% 3.42/1.02      ( r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = iProver_top ),
% 3.42/1.02      inference(demodulation,[status(thm)],[c_0,c_575]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_4,plain,
% 3.42/1.02      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.42/1.02      inference(cnf_transformation,[],[f22]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_577,plain,
% 3.42/1.02      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.42/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1488,plain,
% 3.42/1.02      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))) = sK0 ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_652,c_577]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_7,plain,
% 3.42/1.02      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.42/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_5,plain,
% 3.42/1.02      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 3.42/1.02      inference(cnf_transformation,[],[f31]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_576,plain,
% 3.42/1.02      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 3.42/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_917,plain,
% 3.42/1.02      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_7,c_576]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1591,plain,
% 3.42/1.02      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_0,c_917]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1957,plain,
% 3.42/1.02      ( r1_tarski(sK0,k3_xboole_0(sK0,sK1)) = iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_1488,c_1591]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_2126,plain,
% 3.42/1.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = sK0 ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_1957,c_577]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_6,plain,
% 3.42/1.02      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.42/1.02      inference(cnf_transformation,[],[f32]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1586,plain,
% 3.42/1.02      ( r1_tarski(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),k3_xboole_0(X2,X0)) = iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_0,c_917]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1608,plain,
% 3.42/1.02      ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_6,c_1586]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1942,plain,
% 3.42/1.02      ( r1_tarski(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)) = iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_1488,c_1608]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_2210,plain,
% 3.42/1.02      ( k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)),sK0)) = sK0 ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_1942,c_577]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_3786,plain,
% 3.42/1.02      ( k3_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)))) = sK0 ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_0,c_2210]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_3816,plain,
% 3.42/1.02      ( k3_xboole_0(sK0,sK0) = sK0 ),
% 3.42/1.02      inference(light_normalisation,[status(thm)],[c_3786,c_1488]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_807,plain,
% 3.42/1.02      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_0,c_7]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_5286,plain,
% 3.42/1.02      ( k3_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) = k5_xboole_0(sK0,k3_xboole_0(X0,sK0)) ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_3816,c_807]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_6742,plain,
% 3.42/1.02      ( k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),sK0)) = k3_xboole_0(sK0,k5_xboole_0(sK0,sK0)) ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_2126,c_5286]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_3,plain,
% 3.42/1.02      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.42/1.02      inference(cnf_transformation,[],[f21]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_578,plain,
% 3.42/1.02      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.42/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1486,plain,
% 3.42/1.02      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_578,c_577]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_916,plain,
% 3.42/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_6,c_576]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1,plain,
% 3.42/1.02      ( ~ r1_tarski(X0,X1)
% 3.42/1.02      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.42/1.02      inference(cnf_transformation,[],[f29]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_580,plain,
% 3.42/1.02      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.42/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 3.42/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_3832,plain,
% 3.42/1.02      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_916,c_580]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1490,plain,
% 3.42/1.02      ( k3_xboole_0(X0,X0) = X0 ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_916,c_577]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_3871,plain,
% 3.42/1.02      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.42/1.02      inference(light_normalisation,[status(thm)],[c_3832,c_1490]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1945,plain,
% 3.42/1.02      ( r1_tarski(k5_xboole_0(sK0,sK0),sK0) = iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_1488,c_576]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_2124,plain,
% 3.42/1.02      ( k3_xboole_0(k5_xboole_0(sK0,sK0),sK0) = k5_xboole_0(sK0,sK0) ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_1945,c_577]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_3362,plain,
% 3.42/1.02      ( k3_xboole_0(sK0,k5_xboole_0(sK0,sK0)) = k5_xboole_0(sK0,sK0) ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_2124,c_0]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_4198,plain,
% 3.42/1.02      ( k3_xboole_0(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.42/1.02      inference(demodulation,[status(thm)],[c_3362,c_3871]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_6794,plain,
% 3.42/1.02      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 3.42/1.02      inference(demodulation,[status(thm)],[c_6742,c_1486,c_3871,c_4198]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_8,plain,
% 3.42/1.02      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 3.42/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_9,negated_conjecture,
% 3.42/1.02      ( ~ r1_xboole_0(sK0,sK2) | ~ r1_tarski(sK0,sK1) ),
% 3.42/1.02      inference(cnf_transformation,[],[f28]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_119,plain,
% 3.42/1.02      ( ~ r1_tarski(sK0,sK1)
% 3.42/1.02      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != sK0
% 3.42/1.02      | sK2 != X1 ),
% 3.42/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_120,plain,
% 3.42/1.02      ( ~ r1_tarski(sK0,sK1)
% 3.42/1.02      | k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0 ),
% 3.42/1.02      inference(unflattening,[status(thm)],[c_119]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_574,plain,
% 3.42/1.02      ( k5_xboole_0(X0,k3_xboole_0(X0,sK2)) != sK0
% 3.42/1.02      | r1_tarski(sK0,sK1) != iProver_top ),
% 3.42/1.02      inference(predicate_to_equality,[status(thm)],[c_120]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_812,plain,
% 3.42/1.02      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) != sK0
% 3.42/1.02      | r1_tarski(sK0,sK1) != iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_7,c_574]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1049,plain,
% 3.42/1.02      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(sK2,X1))) != sK0
% 3.42/1.02      | r1_tarski(sK0,sK1) != iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_0,c_812]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_1954,plain,
% 3.42/1.02      ( r1_tarski(sK0,sK1) != iProver_top ),
% 3.42/1.02      inference(superposition,[status(thm)],[c_1488,c_1049]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_2,plain,
% 3.42/1.02      ( r1_tarski(X0,X1)
% 3.42/1.02      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.42/1.02      inference(cnf_transformation,[],[f30]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_590,plain,
% 3.42/1.02      ( r1_tarski(sK0,sK1)
% 3.42/1.02      | k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 3.42/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(c_591,plain,
% 3.42/1.02      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k1_xboole_0
% 3.42/1.02      | r1_tarski(sK0,sK1) = iProver_top ),
% 3.42/1.02      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 3.42/1.02  
% 3.42/1.02  cnf(contradiction,plain,
% 3.42/1.02      ( $false ),
% 3.42/1.02      inference(minisat,[status(thm)],[c_6794,c_1954,c_591]) ).
% 3.42/1.02  
% 3.42/1.02  
% 3.42/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.42/1.02  
% 3.42/1.02  ------                               Statistics
% 3.42/1.02  
% 3.42/1.02  ------ General
% 3.42/1.02  
% 3.42/1.02  abstr_ref_over_cycles:                  0
% 3.42/1.02  abstr_ref_under_cycles:                 0
% 3.42/1.02  gc_basic_clause_elim:                   0
% 3.42/1.02  forced_gc_time:                         0
% 3.42/1.02  parsing_time:                           0.016
% 3.42/1.02  unif_index_cands_time:                  0.
% 3.42/1.02  unif_index_add_time:                    0.
% 3.42/1.02  orderings_time:                         0.
% 3.42/1.02  out_proof_time:                         0.006
% 3.42/1.02  total_time:                             0.25
% 3.42/1.02  num_of_symbols:                         39
% 3.42/1.02  num_of_terms:                           6240
% 3.42/1.02  
% 3.42/1.02  ------ Preprocessing
% 3.42/1.02  
% 3.42/1.02  num_of_splits:                          0
% 3.42/1.02  num_of_split_atoms:                     0
% 3.42/1.02  num_of_reused_defs:                     0
% 3.42/1.02  num_eq_ax_congr_red:                    0
% 3.42/1.02  num_of_sem_filtered_clauses:            1
% 3.42/1.02  num_of_subtypes:                        0
% 3.42/1.02  monotx_restored_types:                  0
% 3.42/1.02  sat_num_of_epr_types:                   0
% 3.42/1.02  sat_num_of_non_cyclic_types:            0
% 3.42/1.02  sat_guarded_non_collapsed_types:        0
% 3.42/1.02  num_pure_diseq_elim:                    0
% 3.42/1.02  simp_replaced_by:                       0
% 3.42/1.02  res_preprocessed:                       52
% 3.42/1.02  prep_upred:                             0
% 3.42/1.02  prep_unflattend:                        33
% 3.42/1.02  smt_new_axioms:                         0
% 3.42/1.02  pred_elim_cands:                        1
% 3.42/1.02  pred_elim:                              1
% 3.42/1.02  pred_elim_cl:                           1
% 3.42/1.02  pred_elim_cycles:                       3
% 3.42/1.02  merged_defs:                            8
% 3.42/1.02  merged_defs_ncl:                        0
% 3.42/1.02  bin_hyper_res:                          8
% 3.42/1.02  prep_cycles:                            4
% 3.42/1.02  pred_elim_time:                         0.004
% 3.42/1.02  splitting_time:                         0.
% 3.42/1.02  sem_filter_time:                        0.
% 3.42/1.02  monotx_time:                            0.001
% 3.42/1.02  subtype_inf_time:                       0.
% 3.42/1.02  
% 3.42/1.02  ------ Problem properties
% 3.42/1.02  
% 3.42/1.02  clauses:                                10
% 3.42/1.02  conjectures:                            1
% 3.42/1.02  epr:                                    0
% 3.42/1.02  horn:                                   10
% 3.42/1.02  ground:                                 1
% 3.42/1.02  unary:                                  6
% 3.42/1.02  binary:                                 4
% 3.42/1.02  lits:                                   14
% 3.42/1.02  lits_eq:                                7
% 3.42/1.02  fd_pure:                                0
% 3.42/1.02  fd_pseudo:                              0
% 3.42/1.02  fd_cond:                                0
% 3.42/1.02  fd_pseudo_cond:                         0
% 3.42/1.02  ac_symbols:                             0
% 3.42/1.02  
% 3.42/1.02  ------ Propositional Solver
% 3.42/1.02  
% 3.42/1.02  prop_solver_calls:                      32
% 3.42/1.02  prop_fast_solver_calls:                 294
% 3.42/1.02  smt_solver_calls:                       0
% 3.42/1.02  smt_fast_solver_calls:                  0
% 3.42/1.02  prop_num_of_clauses:                    2304
% 3.42/1.02  prop_preprocess_simplified:             4458
% 3.42/1.02  prop_fo_subsumed:                       0
% 3.42/1.02  prop_solver_time:                       0.
% 3.42/1.02  smt_solver_time:                        0.
% 3.42/1.02  smt_fast_solver_time:                   0.
% 3.42/1.02  prop_fast_solver_time:                  0.
% 3.42/1.02  prop_unsat_core_time:                   0.
% 3.42/1.02  
% 3.42/1.02  ------ QBF
% 3.42/1.02  
% 3.42/1.02  qbf_q_res:                              0
% 3.42/1.02  qbf_num_tautologies:                    0
% 3.42/1.02  qbf_prep_cycles:                        0
% 3.42/1.02  
% 3.42/1.02  ------ BMC1
% 3.42/1.02  
% 3.42/1.02  bmc1_current_bound:                     -1
% 3.42/1.02  bmc1_last_solved_bound:                 -1
% 3.42/1.02  bmc1_unsat_core_size:                   -1
% 3.42/1.02  bmc1_unsat_core_parents_size:           -1
% 3.42/1.02  bmc1_merge_next_fun:                    0
% 3.42/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.42/1.02  
% 3.42/1.02  ------ Instantiation
% 3.42/1.02  
% 3.42/1.02  inst_num_of_clauses:                    773
% 3.42/1.02  inst_num_in_passive:                    255
% 3.42/1.02  inst_num_in_active:                     317
% 3.42/1.02  inst_num_in_unprocessed:                203
% 3.42/1.02  inst_num_of_loops:                      350
% 3.42/1.02  inst_num_of_learning_restarts:          0
% 3.42/1.02  inst_num_moves_active_passive:          29
% 3.42/1.02  inst_lit_activity:                      0
% 3.42/1.02  inst_lit_activity_moves:                0
% 3.42/1.02  inst_num_tautologies:                   0
% 3.42/1.02  inst_num_prop_implied:                  0
% 3.42/1.02  inst_num_existing_simplified:           0
% 3.42/1.02  inst_num_eq_res_simplified:             0
% 3.42/1.02  inst_num_child_elim:                    0
% 3.42/1.02  inst_num_of_dismatching_blockings:      879
% 3.42/1.02  inst_num_of_non_proper_insts:           1359
% 3.42/1.02  inst_num_of_duplicates:                 0
% 3.42/1.02  inst_inst_num_from_inst_to_res:         0
% 3.42/1.02  inst_dismatching_checking_time:         0.
% 3.42/1.02  
% 3.42/1.02  ------ Resolution
% 3.42/1.02  
% 3.42/1.02  res_num_of_clauses:                     0
% 3.42/1.02  res_num_in_passive:                     0
% 3.42/1.02  res_num_in_active:                      0
% 3.42/1.02  res_num_of_loops:                       56
% 3.42/1.02  res_forward_subset_subsumed:            143
% 3.42/1.02  res_backward_subset_subsumed:           4
% 3.42/1.02  res_forward_subsumed:                   0
% 3.42/1.02  res_backward_subsumed:                  0
% 3.42/1.02  res_forward_subsumption_resolution:     0
% 3.42/1.02  res_backward_subsumption_resolution:    0
% 3.42/1.02  res_clause_to_clause_subsumption:       1968
% 3.42/1.02  res_orphan_elimination:                 0
% 3.42/1.02  res_tautology_del:                      155
% 3.42/1.02  res_num_eq_res_simplified:              0
% 3.42/1.02  res_num_sel_changes:                    0
% 3.42/1.02  res_moves_from_active_to_pass:          0
% 3.42/1.02  
% 3.42/1.02  ------ Superposition
% 3.42/1.02  
% 3.42/1.02  sup_time_total:                         0.
% 3.42/1.02  sup_time_generating:                    0.
% 3.42/1.02  sup_time_sim_full:                      0.
% 3.42/1.02  sup_time_sim_immed:                     0.
% 3.42/1.02  
% 3.42/1.02  sup_num_of_clauses:                     294
% 3.42/1.02  sup_num_in_active:                      58
% 3.42/1.02  sup_num_in_passive:                     236
% 3.42/1.02  sup_num_of_loops:                       68
% 3.42/1.02  sup_fw_superposition:                   363
% 3.42/1.02  sup_bw_superposition:                   448
% 3.42/1.02  sup_immediate_simplified:               276
% 3.42/1.02  sup_given_eliminated:                   0
% 3.42/1.02  comparisons_done:                       0
% 3.42/1.02  comparisons_avoided:                    0
% 3.42/1.02  
% 3.42/1.02  ------ Simplifications
% 3.42/1.02  
% 3.42/1.02  
% 3.42/1.02  sim_fw_subset_subsumed:                 8
% 3.42/1.02  sim_bw_subset_subsumed:                 0
% 3.42/1.02  sim_fw_subsumed:                        72
% 3.42/1.02  sim_bw_subsumed:                        26
% 3.42/1.02  sim_fw_subsumption_res:                 0
% 3.42/1.02  sim_bw_subsumption_res:                 0
% 3.42/1.02  sim_tautology_del:                      0
% 3.42/1.02  sim_eq_tautology_del:                   24
% 3.42/1.02  sim_eq_res_simp:                        1
% 3.42/1.02  sim_fw_demodulated:                     142
% 3.42/1.02  sim_bw_demodulated:                     8
% 3.42/1.02  sim_light_normalised:                   68
% 3.42/1.02  sim_joinable_taut:                      0
% 3.42/1.02  sim_joinable_simp:                      0
% 3.42/1.02  sim_ac_normalised:                      0
% 3.42/1.02  sim_smt_subsumption:                    0
% 3.42/1.02  
%------------------------------------------------------------------------------
