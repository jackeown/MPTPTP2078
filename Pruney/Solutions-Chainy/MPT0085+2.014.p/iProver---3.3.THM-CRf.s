%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:23 EST 2020

% Result     : Theorem 19.77s
% Output     : CNFRefutation 19.77s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 699 expanded)
%              Number of clauses        :   45 ( 275 expanded)
%              Number of leaves         :   12 ( 145 expanded)
%              Depth                    :   24
%              Number of atoms          :  141 (1731 expanded)
%              Number of equality atoms :   62 ( 446 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
      & r1_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    & r1_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f22])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f20])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_256,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_262,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_260,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1392,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_262,c_260])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_258,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14821,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,X1)
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1392,c_258])).

cnf(c_83581,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK3),X0) = k3_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_256,c_14821])).

cnf(c_8,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_83650,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_83581,c_8])).

cnf(c_6,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_84004,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_83650,c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_263,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_653,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_262,c_263])).

cnf(c_786,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_653,c_258])).

cnf(c_881,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_786,c_6])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_889,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_881,c_5])).

cnf(c_455,plain,
    ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_6])).

cnf(c_981,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_889,c_455])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_257,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_787,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_653,c_257])).

cnf(c_1178,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_787,c_258])).

cnf(c_976,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_889])).

cnf(c_2342,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1178,c_976])).

cnf(c_2704,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) = k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[status(thm)],[c_981,c_2342])).

cnf(c_2756,plain,
    ( k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_2704,c_981])).

cnf(c_2796,plain,
    ( k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_2756,c_455])).

cnf(c_2812,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_2796,c_786])).

cnf(c_1179,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_257])).

cnf(c_4279,plain,
    ( r1_tarski(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2812,c_1179])).

cnf(c_4297,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_4279,c_258])).

cnf(c_4459,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)))) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_4297,c_455])).

cnf(c_4474,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_4459,c_2812,c_4297])).

cnf(c_84016,plain,
    ( k3_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k3_xboole_0(sK2,X0) ),
    inference(demodulation,[status(thm)],[c_84004,c_4474])).

cnf(c_10,negated_conjecture,
    ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_88683,plain,
    ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_84016,c_10])).

cnf(c_90,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_580,plain,
    ( k3_xboole_0(sK2,sK4) = k3_xboole_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_88683,c_580])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:15:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 19.77/2.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.77/2.98  
% 19.77/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.77/2.98  
% 19.77/2.98  ------  iProver source info
% 19.77/2.98  
% 19.77/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.77/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.77/2.98  git: non_committed_changes: false
% 19.77/2.98  git: last_make_outside_of_git: false
% 19.77/2.98  
% 19.77/2.98  ------ 
% 19.77/2.98  ------ Parsing...
% 19.77/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.77/2.98  
% 19.77/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.77/2.98  
% 19.77/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.77/2.98  
% 19.77/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.77/2.98  ------ Proving...
% 19.77/2.98  ------ Problem Properties 
% 19.77/2.98  
% 19.77/2.98  
% 19.77/2.98  clauses                                 12
% 19.77/2.98  conjectures                             2
% 19.77/2.98  EPR                                     2
% 19.77/2.98  Horn                                    10
% 19.77/2.98  unary                                   5
% 19.77/2.98  binary                                  6
% 19.77/2.98  lits                                    20
% 19.77/2.98  lits eq                                 5
% 19.77/2.98  fd_pure                                 0
% 19.77/2.98  fd_pseudo                               0
% 19.77/2.98  fd_cond                                 0
% 19.77/2.98  fd_pseudo_cond                          0
% 19.77/2.98  AC symbols                              0
% 19.77/2.98  
% 19.77/2.98  ------ Input Options Time Limit: Unbounded
% 19.77/2.98  
% 19.77/2.98  
% 19.77/2.98  ------ 
% 19.77/2.98  Current options:
% 19.77/2.98  ------ 
% 19.77/2.98  
% 19.77/2.98  
% 19.77/2.98  
% 19.77/2.98  
% 19.77/2.98  ------ Proving...
% 19.77/2.98  
% 19.77/2.98  
% 19.77/2.98  % SZS status Theorem for theBenchmark.p
% 19.77/2.98  
% 19.77/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.77/2.98  
% 19.77/2.98  fof(f8,conjecture,(
% 19.77/2.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 19.77/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.98  
% 19.77/2.98  fof(f9,negated_conjecture,(
% 19.77/2.98    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 19.77/2.98    inference(negated_conjecture,[],[f8])).
% 19.77/2.98  
% 19.77/2.98  fof(f15,plain,(
% 19.77/2.98    ? [X0,X1,X2] : (k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 19.77/2.98    inference(ennf_transformation,[],[f9])).
% 19.77/2.98  
% 19.77/2.98  fof(f22,plain,(
% 19.77/2.98    ? [X0,X1,X2] : (k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) & r1_xboole_0(sK2,sK3))),
% 19.77/2.98    introduced(choice_axiom,[])).
% 19.77/2.98  
% 19.77/2.98  fof(f23,plain,(
% 19.77/2.98    k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) & r1_xboole_0(sK2,sK3)),
% 19.77/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f22])).
% 19.77/2.98  
% 19.77/2.98  fof(f34,plain,(
% 19.77/2.98    r1_xboole_0(sK2,sK3)),
% 19.77/2.98    inference(cnf_transformation,[],[f23])).
% 19.77/2.98  
% 19.77/2.98  fof(f1,axiom,(
% 19.77/2.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.77/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.98  
% 19.77/2.98  fof(f11,plain,(
% 19.77/2.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.77/2.98    inference(ennf_transformation,[],[f1])).
% 19.77/2.98  
% 19.77/2.98  fof(f16,plain,(
% 19.77/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.77/2.98    inference(nnf_transformation,[],[f11])).
% 19.77/2.98  
% 19.77/2.98  fof(f17,plain,(
% 19.77/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.77/2.98    inference(rectify,[],[f16])).
% 19.77/2.98  
% 19.77/2.98  fof(f18,plain,(
% 19.77/2.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.77/2.98    introduced(choice_axiom,[])).
% 19.77/2.98  
% 19.77/2.98  fof(f19,plain,(
% 19.77/2.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.77/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 19.77/2.98  
% 19.77/2.98  fof(f25,plain,(
% 19.77/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.77/2.98    inference(cnf_transformation,[],[f19])).
% 19.77/2.98  
% 19.77/2.98  fof(f2,axiom,(
% 19.77/2.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.77/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.98  
% 19.77/2.98  fof(f10,plain,(
% 19.77/2.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.77/2.98    inference(rectify,[],[f2])).
% 19.77/2.98  
% 19.77/2.98  fof(f12,plain,(
% 19.77/2.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.77/2.98    inference(ennf_transformation,[],[f10])).
% 19.77/2.98  
% 19.77/2.98  fof(f20,plain,(
% 19.77/2.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 19.77/2.98    introduced(choice_axiom,[])).
% 19.77/2.98  
% 19.77/2.98  fof(f21,plain,(
% 19.77/2.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.77/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f20])).
% 19.77/2.98  
% 19.77/2.98  fof(f28,plain,(
% 19.77/2.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 19.77/2.98    inference(cnf_transformation,[],[f21])).
% 19.77/2.98  
% 19.77/2.98  fof(f5,axiom,(
% 19.77/2.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.77/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.98  
% 19.77/2.98  fof(f13,plain,(
% 19.77/2.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.77/2.98    inference(ennf_transformation,[],[f5])).
% 19.77/2.98  
% 19.77/2.98  fof(f31,plain,(
% 19.77/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.77/2.98    inference(cnf_transformation,[],[f13])).
% 19.77/2.98  
% 19.77/2.98  fof(f6,axiom,(
% 19.77/2.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 19.77/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.98  
% 19.77/2.98  fof(f32,plain,(
% 19.77/2.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 19.77/2.98    inference(cnf_transformation,[],[f6])).
% 19.77/2.98  
% 19.77/2.98  fof(f4,axiom,(
% 19.77/2.98    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 19.77/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.98  
% 19.77/2.98  fof(f30,plain,(
% 19.77/2.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 19.77/2.98    inference(cnf_transformation,[],[f4])).
% 19.77/2.98  
% 19.77/2.98  fof(f26,plain,(
% 19.77/2.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 19.77/2.98    inference(cnf_transformation,[],[f19])).
% 19.77/2.98  
% 19.77/2.98  fof(f3,axiom,(
% 19.77/2.98    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 19.77/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.98  
% 19.77/2.98  fof(f29,plain,(
% 19.77/2.98    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 19.77/2.98    inference(cnf_transformation,[],[f3])).
% 19.77/2.98  
% 19.77/2.98  fof(f7,axiom,(
% 19.77/2.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 19.77/2.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/2.98  
% 19.77/2.98  fof(f14,plain,(
% 19.77/2.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 19.77/2.98    inference(ennf_transformation,[],[f7])).
% 19.77/2.98  
% 19.77/2.98  fof(f33,plain,(
% 19.77/2.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 19.77/2.98    inference(cnf_transformation,[],[f14])).
% 19.77/2.98  
% 19.77/2.98  fof(f35,plain,(
% 19.77/2.98    k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),
% 19.77/2.98    inference(cnf_transformation,[],[f23])).
% 19.77/2.98  
% 19.77/2.98  cnf(c_11,negated_conjecture,
% 19.77/2.98      ( r1_xboole_0(sK2,sK3) ),
% 19.77/2.98      inference(cnf_transformation,[],[f34]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_256,plain,
% 19.77/2.98      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 19.77/2.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_1,plain,
% 19.77/2.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.77/2.98      inference(cnf_transformation,[],[f25]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_262,plain,
% 19.77/2.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 19.77/2.98      | r1_tarski(X0,X1) = iProver_top ),
% 19.77/2.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_3,plain,
% 19.77/2.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 19.77/2.98      inference(cnf_transformation,[],[f28]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_260,plain,
% 19.77/2.98      ( r1_xboole_0(X0,X1) != iProver_top
% 19.77/2.98      | r2_hidden(X2,k3_xboole_0(X0,X1)) != iProver_top ),
% 19.77/2.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_1392,plain,
% 19.77/2.98      ( r1_xboole_0(X0,X1) != iProver_top
% 19.77/2.98      | r1_tarski(k3_xboole_0(X0,X1),X2) = iProver_top ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_262,c_260]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_7,plain,
% 19.77/2.98      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 19.77/2.98      inference(cnf_transformation,[],[f31]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_258,plain,
% 19.77/2.98      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 19.77/2.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_14821,plain,
% 19.77/2.98      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,X1)
% 19.77/2.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_1392,c_258]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_83581,plain,
% 19.77/2.98      ( k3_xboole_0(k3_xboole_0(sK2,sK3),X0) = k3_xboole_0(sK2,sK3) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_256,c_14821]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_8,plain,
% 19.77/2.98      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.77/2.98      inference(cnf_transformation,[],[f32]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_83650,plain,
% 19.77/2.98      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_83581,c_8]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_6,plain,
% 19.77/2.98      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 19.77/2.98      inference(cnf_transformation,[],[f30]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_84004,plain,
% 19.77/2.98      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_83650,c_6]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_0,plain,
% 19.77/2.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 19.77/2.98      inference(cnf_transformation,[],[f26]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_263,plain,
% 19.77/2.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 19.77/2.98      | r1_tarski(X0,X1) = iProver_top ),
% 19.77/2.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_653,plain,
% 19.77/2.98      ( r1_tarski(X0,X0) = iProver_top ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_262,c_263]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_786,plain,
% 19.77/2.98      ( k3_xboole_0(X0,X0) = X0 ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_653,c_258]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_881,plain,
% 19.77/2.98      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_786,c_6]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_5,plain,
% 19.77/2.98      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 19.77/2.98      inference(cnf_transformation,[],[f29]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_889,plain,
% 19.77/2.98      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 19.77/2.98      inference(light_normalisation,[status(thm)],[c_881,c_5]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_455,plain,
% 19.77/2.98      ( k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_8,c_6]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_981,plain,
% 19.77/2.98      ( k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) = k2_xboole_0(k1_xboole_0,X0) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_889,c_455]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_9,plain,
% 19.77/2.98      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 19.77/2.98      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 19.77/2.98      inference(cnf_transformation,[],[f33]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_257,plain,
% 19.77/2.98      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 19.77/2.98      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 19.77/2.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_787,plain,
% 19.77/2.98      ( r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_653,c_257]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_1178,plain,
% 19.77/2.98      ( k3_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = X0 ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_787,c_258]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_976,plain,
% 19.77/2.98      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X1,X2))) = k3_xboole_0(X0,X1) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_6,c_889]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_2342,plain,
% 19.77/2.98      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_1178,c_976]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_2704,plain,
% 19.77/2.98      ( k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1))) = k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_981,c_2342]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_2756,plain,
% 19.77/2.98      ( k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),X0) = k2_xboole_0(k1_xboole_0,X0) ),
% 19.77/2.98      inference(light_normalisation,[status(thm)],[c_2704,c_981]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_2796,plain,
% 19.77/2.98      ( k3_xboole_0(k2_xboole_0(k1_xboole_0,X0),k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_2756,c_455]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_2812,plain,
% 19.77/2.98      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 19.77/2.98      inference(demodulation,[status(thm)],[c_2796,c_786]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_1179,plain,
% 19.77/2.98      ( r1_tarski(X0,k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) = iProver_top ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_787,c_257]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_4279,plain,
% 19.77/2.98      ( r1_tarski(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = iProver_top ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_2812,c_1179]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_4297,plain,
% 19.77/2.98      ( k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0))) = X0 ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_4279,c_258]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_4459,plain,
% 19.77/2.98      ( k3_xboole_0(X0,k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0)))) = k2_xboole_0(k1_xboole_0,X0) ),
% 19.77/2.98      inference(superposition,[status(thm)],[c_4297,c_455]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_4474,plain,
% 19.77/2.98      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.77/2.98      inference(demodulation,[status(thm)],[c_4459,c_2812,c_4297]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_84016,plain,
% 19.77/2.98      ( k3_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k3_xboole_0(sK2,X0) ),
% 19.77/2.98      inference(demodulation,[status(thm)],[c_84004,c_4474]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_10,negated_conjecture,
% 19.77/2.98      ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 19.77/2.98      inference(cnf_transformation,[],[f35]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_88683,plain,
% 19.77/2.98      ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,sK4) ),
% 19.77/2.98      inference(demodulation,[status(thm)],[c_84016,c_10]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_90,plain,( X0 = X0 ),theory(equality) ).
% 19.77/2.98  
% 19.77/2.98  cnf(c_580,plain,
% 19.77/2.98      ( k3_xboole_0(sK2,sK4) = k3_xboole_0(sK2,sK4) ),
% 19.77/2.98      inference(instantiation,[status(thm)],[c_90]) ).
% 19.77/2.98  
% 19.77/2.98  cnf(contradiction,plain,
% 19.77/2.98      ( $false ),
% 19.77/2.98      inference(minisat,[status(thm)],[c_88683,c_580]) ).
% 19.77/2.98  
% 19.77/2.98  
% 19.77/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.77/2.98  
% 19.77/2.98  ------                               Statistics
% 19.77/2.98  
% 19.77/2.98  ------ Selected
% 19.77/2.98  
% 19.77/2.98  total_time:                             2.376
% 19.77/2.98  
%------------------------------------------------------------------------------
