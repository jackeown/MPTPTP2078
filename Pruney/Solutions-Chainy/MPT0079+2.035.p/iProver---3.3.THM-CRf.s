%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:51 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 236 expanded)
%              Number of clauses        :   55 (  96 expanded)
%              Number of leaves         :   15 (  60 expanded)
%              Depth                    :   20
%              Number of atoms          :  133 ( 373 expanded)
%              Number of equality atoms :  100 ( 278 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).

fof(f34,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_15,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_100,negated_conjecture,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_15,c_10,c_0])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_272,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_273,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1241,plain,
    ( r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_272,c_273])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_274,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1987,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1241,c_274])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3682,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1987,c_6])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_101,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0])).

cnf(c_518,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_101])).

cnf(c_3688,plain,
    ( k4_xboole_0(sK1,sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_3682,c_4,c_518])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_4024,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_3688,c_8])).

cnf(c_8747,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4024])).

cnf(c_21364,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_100,c_8747])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_288,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_7])).

cnf(c_591,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_288])).

cnf(c_593,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_591,c_6])).

cnf(c_1999,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_593])).

cnf(c_21409,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21364,c_1999])).

cnf(c_21944,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_21409,c_6])).

cnf(c_21954,plain,
    ( k2_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_21944,c_4])).

cnf(c_23422,plain,
    ( k2_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_21954,c_0])).

cnf(c_321,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_10,c_0])).

cnf(c_5511,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_321])).

cnf(c_5514,plain,
    ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_100,c_321])).

cnf(c_6837,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5514,c_593])).

cnf(c_14211,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_xboole_0),k2_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5511,c_6837])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_271,plain,
    ( r1_xboole_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1986,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_271,c_274])).

cnf(c_2635,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1986,c_6])).

cnf(c_2641,plain,
    ( k4_xboole_0(sK2,sK0) = sK2 ),
    inference(demodulation,[status(thm)],[c_2635,c_4,c_518])).

cnf(c_3224,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2641,c_8])).

cnf(c_14230,plain,
    ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14211,c_4,c_3224])).

cnf(c_16216,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_14230,c_6])).

cnf(c_16222,plain,
    ( k2_xboole_0(sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_16216,c_4])).

cnf(c_23455,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_23422,c_16222])).

cnf(c_104,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_332,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_12601,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_332])).

cnf(c_103,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_428,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_12,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23455,c_12601,c_428,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.26/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.26/1.49  
% 7.26/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.26/1.49  
% 7.26/1.49  ------  iProver source info
% 7.26/1.49  
% 7.26/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.26/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.26/1.49  git: non_committed_changes: false
% 7.26/1.49  git: last_make_outside_of_git: false
% 7.26/1.49  
% 7.26/1.49  ------ 
% 7.26/1.49  
% 7.26/1.49  ------ Input Options
% 7.26/1.49  
% 7.26/1.49  --out_options                           all
% 7.26/1.49  --tptp_safe_out                         true
% 7.26/1.49  --problem_path                          ""
% 7.26/1.49  --include_path                          ""
% 7.26/1.49  --clausifier                            res/vclausify_rel
% 7.26/1.49  --clausifier_options                    --mode clausify
% 7.26/1.49  --stdin                                 false
% 7.26/1.49  --stats_out                             all
% 7.26/1.49  
% 7.26/1.49  ------ General Options
% 7.26/1.49  
% 7.26/1.49  --fof                                   false
% 7.26/1.49  --time_out_real                         305.
% 7.26/1.49  --time_out_virtual                      -1.
% 7.26/1.49  --symbol_type_check                     false
% 7.26/1.49  --clausify_out                          false
% 7.26/1.49  --sig_cnt_out                           false
% 7.26/1.49  --trig_cnt_out                          false
% 7.26/1.49  --trig_cnt_out_tolerance                1.
% 7.26/1.49  --trig_cnt_out_sk_spl                   false
% 7.26/1.49  --abstr_cl_out                          false
% 7.26/1.49  
% 7.26/1.49  ------ Global Options
% 7.26/1.49  
% 7.26/1.49  --schedule                              default
% 7.26/1.49  --add_important_lit                     false
% 7.26/1.49  --prop_solver_per_cl                    1000
% 7.26/1.49  --min_unsat_core                        false
% 7.26/1.49  --soft_assumptions                      false
% 7.26/1.49  --soft_lemma_size                       3
% 7.26/1.49  --prop_impl_unit_size                   0
% 7.26/1.49  --prop_impl_unit                        []
% 7.26/1.49  --share_sel_clauses                     true
% 7.26/1.49  --reset_solvers                         false
% 7.26/1.49  --bc_imp_inh                            [conj_cone]
% 7.26/1.49  --conj_cone_tolerance                   3.
% 7.26/1.49  --extra_neg_conj                        none
% 7.26/1.49  --large_theory_mode                     true
% 7.26/1.49  --prolific_symb_bound                   200
% 7.26/1.49  --lt_threshold                          2000
% 7.26/1.49  --clause_weak_htbl                      true
% 7.26/1.49  --gc_record_bc_elim                     false
% 7.26/1.49  
% 7.26/1.49  ------ Preprocessing Options
% 7.26/1.49  
% 7.26/1.49  --preprocessing_flag                    true
% 7.26/1.49  --time_out_prep_mult                    0.1
% 7.26/1.49  --splitting_mode                        input
% 7.26/1.49  --splitting_grd                         true
% 7.26/1.49  --splitting_cvd                         false
% 7.26/1.49  --splitting_cvd_svl                     false
% 7.26/1.49  --splitting_nvd                         32
% 7.26/1.49  --sub_typing                            true
% 7.26/1.49  --prep_gs_sim                           true
% 7.26/1.49  --prep_unflatten                        true
% 7.26/1.49  --prep_res_sim                          true
% 7.26/1.49  --prep_upred                            true
% 7.26/1.49  --prep_sem_filter                       exhaustive
% 7.26/1.49  --prep_sem_filter_out                   false
% 7.26/1.49  --pred_elim                             true
% 7.26/1.49  --res_sim_input                         true
% 7.26/1.49  --eq_ax_congr_red                       true
% 7.26/1.49  --pure_diseq_elim                       true
% 7.26/1.49  --brand_transform                       false
% 7.26/1.49  --non_eq_to_eq                          false
% 7.26/1.49  --prep_def_merge                        true
% 7.26/1.49  --prep_def_merge_prop_impl              false
% 7.26/1.49  --prep_def_merge_mbd                    true
% 7.26/1.49  --prep_def_merge_tr_red                 false
% 7.26/1.49  --prep_def_merge_tr_cl                  false
% 7.26/1.49  --smt_preprocessing                     true
% 7.26/1.49  --smt_ac_axioms                         fast
% 7.26/1.49  --preprocessed_out                      false
% 7.26/1.49  --preprocessed_stats                    false
% 7.26/1.49  
% 7.26/1.49  ------ Abstraction refinement Options
% 7.26/1.49  
% 7.26/1.49  --abstr_ref                             []
% 7.26/1.49  --abstr_ref_prep                        false
% 7.26/1.49  --abstr_ref_until_sat                   false
% 7.26/1.49  --abstr_ref_sig_restrict                funpre
% 7.26/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.49  --abstr_ref_under                       []
% 7.26/1.49  
% 7.26/1.49  ------ SAT Options
% 7.26/1.49  
% 7.26/1.49  --sat_mode                              false
% 7.26/1.49  --sat_fm_restart_options                ""
% 7.26/1.49  --sat_gr_def                            false
% 7.26/1.49  --sat_epr_types                         true
% 7.26/1.49  --sat_non_cyclic_types                  false
% 7.26/1.49  --sat_finite_models                     false
% 7.26/1.49  --sat_fm_lemmas                         false
% 7.26/1.49  --sat_fm_prep                           false
% 7.26/1.49  --sat_fm_uc_incr                        true
% 7.26/1.49  --sat_out_model                         small
% 7.26/1.49  --sat_out_clauses                       false
% 7.26/1.49  
% 7.26/1.49  ------ QBF Options
% 7.26/1.49  
% 7.26/1.49  --qbf_mode                              false
% 7.26/1.49  --qbf_elim_univ                         false
% 7.26/1.49  --qbf_dom_inst                          none
% 7.26/1.49  --qbf_dom_pre_inst                      false
% 7.26/1.49  --qbf_sk_in                             false
% 7.26/1.49  --qbf_pred_elim                         true
% 7.26/1.49  --qbf_split                             512
% 7.26/1.49  
% 7.26/1.49  ------ BMC1 Options
% 7.26/1.49  
% 7.26/1.49  --bmc1_incremental                      false
% 7.26/1.49  --bmc1_axioms                           reachable_all
% 7.26/1.49  --bmc1_min_bound                        0
% 7.26/1.49  --bmc1_max_bound                        -1
% 7.26/1.49  --bmc1_max_bound_default                -1
% 7.26/1.49  --bmc1_symbol_reachability              true
% 7.26/1.49  --bmc1_property_lemmas                  false
% 7.26/1.49  --bmc1_k_induction                      false
% 7.26/1.49  --bmc1_non_equiv_states                 false
% 7.26/1.49  --bmc1_deadlock                         false
% 7.26/1.49  --bmc1_ucm                              false
% 7.26/1.49  --bmc1_add_unsat_core                   none
% 7.26/1.49  --bmc1_unsat_core_children              false
% 7.26/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.49  --bmc1_out_stat                         full
% 7.26/1.49  --bmc1_ground_init                      false
% 7.26/1.49  --bmc1_pre_inst_next_state              false
% 7.26/1.49  --bmc1_pre_inst_state                   false
% 7.26/1.49  --bmc1_pre_inst_reach_state             false
% 7.26/1.49  --bmc1_out_unsat_core                   false
% 7.26/1.49  --bmc1_aig_witness_out                  false
% 7.26/1.49  --bmc1_verbose                          false
% 7.26/1.49  --bmc1_dump_clauses_tptp                false
% 7.26/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.49  --bmc1_dump_file                        -
% 7.26/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.49  --bmc1_ucm_extend_mode                  1
% 7.26/1.49  --bmc1_ucm_init_mode                    2
% 7.26/1.49  --bmc1_ucm_cone_mode                    none
% 7.26/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.49  --bmc1_ucm_relax_model                  4
% 7.26/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.49  --bmc1_ucm_layered_model                none
% 7.26/1.49  --bmc1_ucm_max_lemma_size               10
% 7.26/1.49  
% 7.26/1.49  ------ AIG Options
% 7.26/1.49  
% 7.26/1.49  --aig_mode                              false
% 7.26/1.49  
% 7.26/1.49  ------ Instantiation Options
% 7.26/1.49  
% 7.26/1.49  --instantiation_flag                    true
% 7.26/1.49  --inst_sos_flag                         false
% 7.26/1.49  --inst_sos_phase                        true
% 7.26/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.49  --inst_lit_sel_side                     num_symb
% 7.26/1.49  --inst_solver_per_active                1400
% 7.26/1.49  --inst_solver_calls_frac                1.
% 7.26/1.49  --inst_passive_queue_type               priority_queues
% 7.26/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.49  --inst_passive_queues_freq              [25;2]
% 7.26/1.49  --inst_dismatching                      true
% 7.26/1.49  --inst_eager_unprocessed_to_passive     true
% 7.26/1.49  --inst_prop_sim_given                   true
% 7.26/1.49  --inst_prop_sim_new                     false
% 7.26/1.49  --inst_subs_new                         false
% 7.26/1.49  --inst_eq_res_simp                      false
% 7.26/1.49  --inst_subs_given                       false
% 7.26/1.49  --inst_orphan_elimination               true
% 7.26/1.49  --inst_learning_loop_flag               true
% 7.26/1.49  --inst_learning_start                   3000
% 7.26/1.49  --inst_learning_factor                  2
% 7.26/1.49  --inst_start_prop_sim_after_learn       3
% 7.26/1.49  --inst_sel_renew                        solver
% 7.26/1.49  --inst_lit_activity_flag                true
% 7.26/1.49  --inst_restr_to_given                   false
% 7.26/1.49  --inst_activity_threshold               500
% 7.26/1.49  --inst_out_proof                        true
% 7.26/1.49  
% 7.26/1.49  ------ Resolution Options
% 7.26/1.49  
% 7.26/1.49  --resolution_flag                       true
% 7.26/1.49  --res_lit_sel                           adaptive
% 7.26/1.49  --res_lit_sel_side                      none
% 7.26/1.49  --res_ordering                          kbo
% 7.26/1.49  --res_to_prop_solver                    active
% 7.26/1.49  --res_prop_simpl_new                    false
% 7.26/1.49  --res_prop_simpl_given                  true
% 7.26/1.49  --res_passive_queue_type                priority_queues
% 7.26/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.50  --res_passive_queues_freq               [15;5]
% 7.26/1.50  --res_forward_subs                      full
% 7.26/1.50  --res_backward_subs                     full
% 7.26/1.50  --res_forward_subs_resolution           true
% 7.26/1.50  --res_backward_subs_resolution          true
% 7.26/1.50  --res_orphan_elimination                true
% 7.26/1.50  --res_time_limit                        2.
% 7.26/1.50  --res_out_proof                         true
% 7.26/1.50  
% 7.26/1.50  ------ Superposition Options
% 7.26/1.50  
% 7.26/1.50  --superposition_flag                    true
% 7.26/1.50  --sup_passive_queue_type                priority_queues
% 7.26/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.50  --demod_completeness_check              fast
% 7.26/1.50  --demod_use_ground                      true
% 7.26/1.50  --sup_to_prop_solver                    passive
% 7.26/1.50  --sup_prop_simpl_new                    true
% 7.26/1.50  --sup_prop_simpl_given                  true
% 7.26/1.50  --sup_fun_splitting                     false
% 7.26/1.50  --sup_smt_interval                      50000
% 7.26/1.50  
% 7.26/1.50  ------ Superposition Simplification Setup
% 7.26/1.50  
% 7.26/1.50  --sup_indices_passive                   []
% 7.26/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_full_bw                           [BwDemod]
% 7.26/1.50  --sup_immed_triv                        [TrivRules]
% 7.26/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_immed_bw_main                     []
% 7.26/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.50  
% 7.26/1.50  ------ Combination Options
% 7.26/1.50  
% 7.26/1.50  --comb_res_mult                         3
% 7.26/1.50  --comb_sup_mult                         2
% 7.26/1.50  --comb_inst_mult                        10
% 7.26/1.50  
% 7.26/1.50  ------ Debug Options
% 7.26/1.50  
% 7.26/1.50  --dbg_backtrace                         false
% 7.26/1.50  --dbg_dump_prop_clauses                 false
% 7.26/1.50  --dbg_dump_prop_clauses_file            -
% 7.26/1.50  --dbg_out_stat                          false
% 7.26/1.50  ------ Parsing...
% 7.26/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.26/1.50  ------ Proving...
% 7.26/1.50  ------ Problem Properties 
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  clauses                                 16
% 7.26/1.50  conjectures                             4
% 7.26/1.50  EPR                                     4
% 7.26/1.50  Horn                                    16
% 7.26/1.50  unary                                   13
% 7.26/1.50  binary                                  3
% 7.26/1.50  lits                                    19
% 7.26/1.50  lits eq                                 13
% 7.26/1.50  fd_pure                                 0
% 7.26/1.50  fd_pseudo                               0
% 7.26/1.50  fd_cond                                 0
% 7.26/1.50  fd_pseudo_cond                          0
% 7.26/1.50  AC symbols                              1
% 7.26/1.50  
% 7.26/1.50  ------ Schedule dynamic 5 is on 
% 7.26/1.50  
% 7.26/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  ------ 
% 7.26/1.50  Current options:
% 7.26/1.50  ------ 
% 7.26/1.50  
% 7.26/1.50  ------ Input Options
% 7.26/1.50  
% 7.26/1.50  --out_options                           all
% 7.26/1.50  --tptp_safe_out                         true
% 7.26/1.50  --problem_path                          ""
% 7.26/1.50  --include_path                          ""
% 7.26/1.50  --clausifier                            res/vclausify_rel
% 7.26/1.50  --clausifier_options                    --mode clausify
% 7.26/1.50  --stdin                                 false
% 7.26/1.50  --stats_out                             all
% 7.26/1.50  
% 7.26/1.50  ------ General Options
% 7.26/1.50  
% 7.26/1.50  --fof                                   false
% 7.26/1.50  --time_out_real                         305.
% 7.26/1.50  --time_out_virtual                      -1.
% 7.26/1.50  --symbol_type_check                     false
% 7.26/1.50  --clausify_out                          false
% 7.26/1.50  --sig_cnt_out                           false
% 7.26/1.50  --trig_cnt_out                          false
% 7.26/1.50  --trig_cnt_out_tolerance                1.
% 7.26/1.50  --trig_cnt_out_sk_spl                   false
% 7.26/1.50  --abstr_cl_out                          false
% 7.26/1.50  
% 7.26/1.50  ------ Global Options
% 7.26/1.50  
% 7.26/1.50  --schedule                              default
% 7.26/1.50  --add_important_lit                     false
% 7.26/1.50  --prop_solver_per_cl                    1000
% 7.26/1.50  --min_unsat_core                        false
% 7.26/1.50  --soft_assumptions                      false
% 7.26/1.50  --soft_lemma_size                       3
% 7.26/1.50  --prop_impl_unit_size                   0
% 7.26/1.50  --prop_impl_unit                        []
% 7.26/1.50  --share_sel_clauses                     true
% 7.26/1.50  --reset_solvers                         false
% 7.26/1.50  --bc_imp_inh                            [conj_cone]
% 7.26/1.50  --conj_cone_tolerance                   3.
% 7.26/1.50  --extra_neg_conj                        none
% 7.26/1.50  --large_theory_mode                     true
% 7.26/1.50  --prolific_symb_bound                   200
% 7.26/1.50  --lt_threshold                          2000
% 7.26/1.50  --clause_weak_htbl                      true
% 7.26/1.50  --gc_record_bc_elim                     false
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing Options
% 7.26/1.50  
% 7.26/1.50  --preprocessing_flag                    true
% 7.26/1.50  --time_out_prep_mult                    0.1
% 7.26/1.50  --splitting_mode                        input
% 7.26/1.50  --splitting_grd                         true
% 7.26/1.50  --splitting_cvd                         false
% 7.26/1.50  --splitting_cvd_svl                     false
% 7.26/1.50  --splitting_nvd                         32
% 7.26/1.50  --sub_typing                            true
% 7.26/1.50  --prep_gs_sim                           true
% 7.26/1.50  --prep_unflatten                        true
% 7.26/1.50  --prep_res_sim                          true
% 7.26/1.50  --prep_upred                            true
% 7.26/1.50  --prep_sem_filter                       exhaustive
% 7.26/1.50  --prep_sem_filter_out                   false
% 7.26/1.50  --pred_elim                             true
% 7.26/1.50  --res_sim_input                         true
% 7.26/1.50  --eq_ax_congr_red                       true
% 7.26/1.50  --pure_diseq_elim                       true
% 7.26/1.50  --brand_transform                       false
% 7.26/1.50  --non_eq_to_eq                          false
% 7.26/1.50  --prep_def_merge                        true
% 7.26/1.50  --prep_def_merge_prop_impl              false
% 7.26/1.50  --prep_def_merge_mbd                    true
% 7.26/1.50  --prep_def_merge_tr_red                 false
% 7.26/1.50  --prep_def_merge_tr_cl                  false
% 7.26/1.50  --smt_preprocessing                     true
% 7.26/1.50  --smt_ac_axioms                         fast
% 7.26/1.50  --preprocessed_out                      false
% 7.26/1.50  --preprocessed_stats                    false
% 7.26/1.50  
% 7.26/1.50  ------ Abstraction refinement Options
% 7.26/1.50  
% 7.26/1.50  --abstr_ref                             []
% 7.26/1.50  --abstr_ref_prep                        false
% 7.26/1.50  --abstr_ref_until_sat                   false
% 7.26/1.50  --abstr_ref_sig_restrict                funpre
% 7.26/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.50  --abstr_ref_under                       []
% 7.26/1.50  
% 7.26/1.50  ------ SAT Options
% 7.26/1.50  
% 7.26/1.50  --sat_mode                              false
% 7.26/1.50  --sat_fm_restart_options                ""
% 7.26/1.50  --sat_gr_def                            false
% 7.26/1.50  --sat_epr_types                         true
% 7.26/1.50  --sat_non_cyclic_types                  false
% 7.26/1.50  --sat_finite_models                     false
% 7.26/1.50  --sat_fm_lemmas                         false
% 7.26/1.50  --sat_fm_prep                           false
% 7.26/1.50  --sat_fm_uc_incr                        true
% 7.26/1.50  --sat_out_model                         small
% 7.26/1.50  --sat_out_clauses                       false
% 7.26/1.50  
% 7.26/1.50  ------ QBF Options
% 7.26/1.50  
% 7.26/1.50  --qbf_mode                              false
% 7.26/1.50  --qbf_elim_univ                         false
% 7.26/1.50  --qbf_dom_inst                          none
% 7.26/1.50  --qbf_dom_pre_inst                      false
% 7.26/1.50  --qbf_sk_in                             false
% 7.26/1.50  --qbf_pred_elim                         true
% 7.26/1.50  --qbf_split                             512
% 7.26/1.50  
% 7.26/1.50  ------ BMC1 Options
% 7.26/1.50  
% 7.26/1.50  --bmc1_incremental                      false
% 7.26/1.50  --bmc1_axioms                           reachable_all
% 7.26/1.50  --bmc1_min_bound                        0
% 7.26/1.50  --bmc1_max_bound                        -1
% 7.26/1.50  --bmc1_max_bound_default                -1
% 7.26/1.50  --bmc1_symbol_reachability              true
% 7.26/1.50  --bmc1_property_lemmas                  false
% 7.26/1.50  --bmc1_k_induction                      false
% 7.26/1.50  --bmc1_non_equiv_states                 false
% 7.26/1.50  --bmc1_deadlock                         false
% 7.26/1.50  --bmc1_ucm                              false
% 7.26/1.50  --bmc1_add_unsat_core                   none
% 7.26/1.50  --bmc1_unsat_core_children              false
% 7.26/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.50  --bmc1_out_stat                         full
% 7.26/1.50  --bmc1_ground_init                      false
% 7.26/1.50  --bmc1_pre_inst_next_state              false
% 7.26/1.50  --bmc1_pre_inst_state                   false
% 7.26/1.50  --bmc1_pre_inst_reach_state             false
% 7.26/1.50  --bmc1_out_unsat_core                   false
% 7.26/1.50  --bmc1_aig_witness_out                  false
% 7.26/1.50  --bmc1_verbose                          false
% 7.26/1.50  --bmc1_dump_clauses_tptp                false
% 7.26/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.50  --bmc1_dump_file                        -
% 7.26/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.50  --bmc1_ucm_extend_mode                  1
% 7.26/1.50  --bmc1_ucm_init_mode                    2
% 7.26/1.50  --bmc1_ucm_cone_mode                    none
% 7.26/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.50  --bmc1_ucm_relax_model                  4
% 7.26/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.50  --bmc1_ucm_layered_model                none
% 7.26/1.50  --bmc1_ucm_max_lemma_size               10
% 7.26/1.50  
% 7.26/1.50  ------ AIG Options
% 7.26/1.50  
% 7.26/1.50  --aig_mode                              false
% 7.26/1.50  
% 7.26/1.50  ------ Instantiation Options
% 7.26/1.50  
% 7.26/1.50  --instantiation_flag                    true
% 7.26/1.50  --inst_sos_flag                         false
% 7.26/1.50  --inst_sos_phase                        true
% 7.26/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.50  --inst_lit_sel_side                     none
% 7.26/1.50  --inst_solver_per_active                1400
% 7.26/1.50  --inst_solver_calls_frac                1.
% 7.26/1.50  --inst_passive_queue_type               priority_queues
% 7.26/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.50  --inst_passive_queues_freq              [25;2]
% 7.26/1.50  --inst_dismatching                      true
% 7.26/1.50  --inst_eager_unprocessed_to_passive     true
% 7.26/1.50  --inst_prop_sim_given                   true
% 7.26/1.50  --inst_prop_sim_new                     false
% 7.26/1.50  --inst_subs_new                         false
% 7.26/1.50  --inst_eq_res_simp                      false
% 7.26/1.50  --inst_subs_given                       false
% 7.26/1.50  --inst_orphan_elimination               true
% 7.26/1.50  --inst_learning_loop_flag               true
% 7.26/1.50  --inst_learning_start                   3000
% 7.26/1.50  --inst_learning_factor                  2
% 7.26/1.50  --inst_start_prop_sim_after_learn       3
% 7.26/1.50  --inst_sel_renew                        solver
% 7.26/1.50  --inst_lit_activity_flag                true
% 7.26/1.50  --inst_restr_to_given                   false
% 7.26/1.50  --inst_activity_threshold               500
% 7.26/1.50  --inst_out_proof                        true
% 7.26/1.50  
% 7.26/1.50  ------ Resolution Options
% 7.26/1.50  
% 7.26/1.50  --resolution_flag                       false
% 7.26/1.50  --res_lit_sel                           adaptive
% 7.26/1.50  --res_lit_sel_side                      none
% 7.26/1.50  --res_ordering                          kbo
% 7.26/1.50  --res_to_prop_solver                    active
% 7.26/1.50  --res_prop_simpl_new                    false
% 7.26/1.50  --res_prop_simpl_given                  true
% 7.26/1.50  --res_passive_queue_type                priority_queues
% 7.26/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.50  --res_passive_queues_freq               [15;5]
% 7.26/1.50  --res_forward_subs                      full
% 7.26/1.50  --res_backward_subs                     full
% 7.26/1.50  --res_forward_subs_resolution           true
% 7.26/1.50  --res_backward_subs_resolution          true
% 7.26/1.50  --res_orphan_elimination                true
% 7.26/1.50  --res_time_limit                        2.
% 7.26/1.50  --res_out_proof                         true
% 7.26/1.50  
% 7.26/1.50  ------ Superposition Options
% 7.26/1.50  
% 7.26/1.50  --superposition_flag                    true
% 7.26/1.50  --sup_passive_queue_type                priority_queues
% 7.26/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.50  --demod_completeness_check              fast
% 7.26/1.50  --demod_use_ground                      true
% 7.26/1.50  --sup_to_prop_solver                    passive
% 7.26/1.50  --sup_prop_simpl_new                    true
% 7.26/1.50  --sup_prop_simpl_given                  true
% 7.26/1.50  --sup_fun_splitting                     false
% 7.26/1.50  --sup_smt_interval                      50000
% 7.26/1.50  
% 7.26/1.50  ------ Superposition Simplification Setup
% 7.26/1.50  
% 7.26/1.50  --sup_indices_passive                   []
% 7.26/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_full_bw                           [BwDemod]
% 7.26/1.50  --sup_immed_triv                        [TrivRules]
% 7.26/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_immed_bw_main                     []
% 7.26/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.26/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.26/1.50  
% 7.26/1.50  ------ Combination Options
% 7.26/1.50  
% 7.26/1.50  --comb_res_mult                         3
% 7.26/1.50  --comb_sup_mult                         2
% 7.26/1.50  --comb_inst_mult                        10
% 7.26/1.50  
% 7.26/1.50  ------ Debug Options
% 7.26/1.50  
% 7.26/1.50  --dbg_backtrace                         false
% 7.26/1.50  --dbg_dump_prop_clauses                 false
% 7.26/1.50  --dbg_dump_prop_clauses_file            -
% 7.26/1.50  --dbg_out_stat                          false
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  ------ Proving...
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  % SZS status Theorem for theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  fof(f13,conjecture,(
% 7.26/1.50    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f14,negated_conjecture,(
% 7.26/1.50    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 7.26/1.50    inference(negated_conjecture,[],[f13])).
% 7.26/1.50  
% 7.26/1.50  fof(f16,plain,(
% 7.26/1.50    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 7.26/1.50    inference(ennf_transformation,[],[f14])).
% 7.26/1.50  
% 7.26/1.50  fof(f17,plain,(
% 7.26/1.50    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 7.26/1.50    inference(flattening,[],[f16])).
% 7.26/1.50  
% 7.26/1.50  fof(f19,plain,(
% 7.26/1.50    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 7.26/1.50    introduced(choice_axiom,[])).
% 7.26/1.50  
% 7.26/1.50  fof(f20,plain,(
% 7.26/1.50    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 7.26/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f19])).
% 7.26/1.50  
% 7.26/1.50  fof(f34,plain,(
% 7.26/1.50    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 7.26/1.50    inference(cnf_transformation,[],[f20])).
% 7.26/1.50  
% 7.26/1.50  fof(f11,axiom,(
% 7.26/1.50    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f32,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f11])).
% 7.26/1.50  
% 7.26/1.50  fof(f1,axiom,(
% 7.26/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f21,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f1])).
% 7.26/1.50  
% 7.26/1.50  fof(f36,plain,(
% 7.26/1.50    r1_xboole_0(sK3,sK1)),
% 7.26/1.50    inference(cnf_transformation,[],[f20])).
% 7.26/1.50  
% 7.26/1.50  fof(f3,axiom,(
% 7.26/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f15,plain,(
% 7.26/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.26/1.50    inference(ennf_transformation,[],[f3])).
% 7.26/1.50  
% 7.26/1.50  fof(f24,plain,(
% 7.26/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f15])).
% 7.26/1.50  
% 7.26/1.50  fof(f2,axiom,(
% 7.26/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f18,plain,(
% 7.26/1.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.26/1.50    inference(nnf_transformation,[],[f2])).
% 7.26/1.50  
% 7.26/1.50  fof(f22,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f18])).
% 7.26/1.50  
% 7.26/1.50  fof(f10,axiom,(
% 7.26/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f31,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f10])).
% 7.26/1.50  
% 7.26/1.50  fof(f39,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.26/1.50    inference(definition_unfolding,[],[f22,f31])).
% 7.26/1.50  
% 7.26/1.50  fof(f6,axiom,(
% 7.26/1.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f27,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.26/1.50    inference(cnf_transformation,[],[f6])).
% 7.26/1.50  
% 7.26/1.50  fof(f4,axiom,(
% 7.26/1.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f25,plain,(
% 7.26/1.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.26/1.50    inference(cnf_transformation,[],[f4])).
% 7.26/1.50  
% 7.26/1.50  fof(f12,axiom,(
% 7.26/1.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f33,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.26/1.50    inference(cnf_transformation,[],[f12])).
% 7.26/1.50  
% 7.26/1.50  fof(f41,plain,(
% 7.26/1.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 7.26/1.50    inference(definition_unfolding,[],[f33,f31])).
% 7.26/1.50  
% 7.26/1.50  fof(f8,axiom,(
% 7.26/1.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f29,plain,(
% 7.26/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.26/1.50    inference(cnf_transformation,[],[f8])).
% 7.26/1.50  
% 7.26/1.50  fof(f5,axiom,(
% 7.26/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f26,plain,(
% 7.26/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.26/1.50    inference(cnf_transformation,[],[f5])).
% 7.26/1.50  
% 7.26/1.50  fof(f40,plain,(
% 7.26/1.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.26/1.50    inference(definition_unfolding,[],[f26,f31])).
% 7.26/1.50  
% 7.26/1.50  fof(f7,axiom,(
% 7.26/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.26/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.26/1.50  
% 7.26/1.50  fof(f28,plain,(
% 7.26/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.26/1.50    inference(cnf_transformation,[],[f7])).
% 7.26/1.50  
% 7.26/1.50  fof(f35,plain,(
% 7.26/1.50    r1_xboole_0(sK2,sK0)),
% 7.26/1.50    inference(cnf_transformation,[],[f20])).
% 7.26/1.50  
% 7.26/1.50  fof(f37,plain,(
% 7.26/1.50    sK1 != sK2),
% 7.26/1.50    inference(cnf_transformation,[],[f20])).
% 7.26/1.50  
% 7.26/1.50  cnf(c_15,negated_conjecture,
% 7.26/1.50      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 7.26/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_10,plain,
% 7.26/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.26/1.50      inference(cnf_transformation,[],[f32]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_0,plain,
% 7.26/1.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f21]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_100,negated_conjecture,
% 7.26/1.50      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 7.26/1.50      inference(theory_normalisation,[status(thm)],[c_15,c_10,c_0]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_13,negated_conjecture,
% 7.26/1.50      ( r1_xboole_0(sK3,sK1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_272,plain,
% 7.26/1.50      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3,plain,
% 7.26/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f24]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_273,plain,
% 7.26/1.50      ( r1_xboole_0(X0,X1) != iProver_top
% 7.26/1.50      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1241,plain,
% 7.26/1.50      ( r1_xboole_0(sK1,sK3) = iProver_top ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_272,c_273]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2,plain,
% 7.26/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.26/1.50      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.26/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_274,plain,
% 7.26/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.26/1.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1987,plain,
% 7.26/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k1_xboole_0 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_1241,c_274]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6,plain,
% 7.26/1.50      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.26/1.50      inference(cnf_transformation,[],[f27]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3682,plain,
% 7.26/1.50      ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_1987,c_6]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4,plain,
% 7.26/1.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.26/1.50      inference(cnf_transformation,[],[f25]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_11,plain,
% 7.26/1.50      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 7.26/1.50      inference(cnf_transformation,[],[f41]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_101,plain,
% 7.26/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 7.26/1.50      inference(theory_normalisation,[status(thm)],[c_11,c_10,c_0]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_518,plain,
% 7.26/1.50      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_6,c_101]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3688,plain,
% 7.26/1.50      ( k4_xboole_0(sK1,sK3) = sK1 ),
% 7.26/1.50      inference(demodulation,[status(thm)],[c_3682,c_4,c_518]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_8,plain,
% 7.26/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.26/1.50      inference(cnf_transformation,[],[f29]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_4024,plain,
% 7.26/1.50      ( k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_3688,c_8]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_8747,plain,
% 7.26/1.50      ( k4_xboole_0(sK1,k2_xboole_0(X0,sK3)) = k4_xboole_0(sK1,X0) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_0,c_4024]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_21364,plain,
% 7.26/1.50      ( k4_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK1,sK2) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_100,c_8747]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5,plain,
% 7.26/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.26/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_7,plain,
% 7.26/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.26/1.50      inference(cnf_transformation,[],[f28]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_288,plain,
% 7.26/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.26/1.50      inference(light_normalisation,[status(thm)],[c_5,c_7]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_591,plain,
% 7.26/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_8,c_288]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_593,plain,
% 7.26/1.50      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.26/1.50      inference(demodulation,[status(thm)],[c_591,c_6]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1999,plain,
% 7.26/1.50      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_0,c_593]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_21409,plain,
% 7.26/1.50      ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 7.26/1.50      inference(demodulation,[status(thm)],[c_21364,c_1999]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_21944,plain,
% 7.26/1.50      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_21409,c_6]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_21954,plain,
% 7.26/1.50      ( k2_xboole_0(sK2,sK1) = sK2 ),
% 7.26/1.50      inference(demodulation,[status(thm)],[c_21944,c_4]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_23422,plain,
% 7.26/1.50      ( k2_xboole_0(sK1,sK2) = sK2 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_21954,c_0]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_321,plain,
% 7.26/1.50      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_10,c_0]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5511,plain,
% 7.26/1.50      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_4,c_321]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_5514,plain,
% 7.26/1.50      ( k2_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k2_xboole_0(X0,k2_xboole_0(sK1,sK0)) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_100,c_321]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_6837,plain,
% 7.26/1.50      ( k4_xboole_0(k2_xboole_0(sK2,X0),k2_xboole_0(X0,k2_xboole_0(sK1,sK0))) = k1_xboole_0 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_5514,c_593]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_14211,plain,
% 7.26/1.50      ( k4_xboole_0(k2_xboole_0(sK2,k1_xboole_0),k2_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_5511,c_6837]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_14,negated_conjecture,
% 7.26/1.50      ( r1_xboole_0(sK2,sK0) ),
% 7.26/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_271,plain,
% 7.26/1.50      ( r1_xboole_0(sK2,sK0) = iProver_top ),
% 7.26/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_1986,plain,
% 7.26/1.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k1_xboole_0 ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_271,c_274]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2635,plain,
% 7.26/1.50      ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_1986,c_6]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_2641,plain,
% 7.26/1.50      ( k4_xboole_0(sK2,sK0) = sK2 ),
% 7.26/1.50      inference(demodulation,[status(thm)],[c_2635,c_4,c_518]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_3224,plain,
% 7.26/1.50      ( k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_2641,c_8]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_14230,plain,
% 7.26/1.50      ( k4_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 7.26/1.50      inference(demodulation,[status(thm)],[c_14211,c_4,c_3224]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_16216,plain,
% 7.26/1.50      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k1_xboole_0) ),
% 7.26/1.50      inference(superposition,[status(thm)],[c_14230,c_6]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_16222,plain,
% 7.26/1.50      ( k2_xboole_0(sK1,sK2) = sK1 ),
% 7.26/1.50      inference(demodulation,[status(thm)],[c_16216,c_4]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_23455,plain,
% 7.26/1.50      ( sK2 = sK1 ),
% 7.26/1.50      inference(light_normalisation,[status(thm)],[c_23422,c_16222]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_104,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_332,plain,
% 7.26/1.50      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_104]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_12601,plain,
% 7.26/1.50      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_332]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_103,plain,( X0 = X0 ),theory(equality) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_428,plain,
% 7.26/1.50      ( sK1 = sK1 ),
% 7.26/1.50      inference(instantiation,[status(thm)],[c_103]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(c_12,negated_conjecture,
% 7.26/1.50      ( sK1 != sK2 ),
% 7.26/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.26/1.50  
% 7.26/1.50  cnf(contradiction,plain,
% 7.26/1.50      ( $false ),
% 7.26/1.50      inference(minisat,[status(thm)],[c_23455,c_12601,c_428,c_12]) ).
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.26/1.50  
% 7.26/1.50  ------                               Statistics
% 7.26/1.50  
% 7.26/1.50  ------ General
% 7.26/1.50  
% 7.26/1.50  abstr_ref_over_cycles:                  0
% 7.26/1.50  abstr_ref_under_cycles:                 0
% 7.26/1.50  gc_basic_clause_elim:                   0
% 7.26/1.50  forced_gc_time:                         0
% 7.26/1.50  parsing_time:                           0.006
% 7.26/1.50  unif_index_cands_time:                  0.
% 7.26/1.50  unif_index_add_time:                    0.
% 7.26/1.50  orderings_time:                         0.
% 7.26/1.50  out_proof_time:                         0.006
% 7.26/1.50  total_time:                             0.627
% 7.26/1.50  num_of_symbols:                         39
% 7.26/1.50  num_of_terms:                           29869
% 7.26/1.50  
% 7.26/1.50  ------ Preprocessing
% 7.26/1.50  
% 7.26/1.50  num_of_splits:                          0
% 7.26/1.50  num_of_split_atoms:                     0
% 7.26/1.50  num_of_reused_defs:                     0
% 7.26/1.50  num_eq_ax_congr_red:                    0
% 7.26/1.50  num_of_sem_filtered_clauses:            1
% 7.26/1.50  num_of_subtypes:                        0
% 7.26/1.50  monotx_restored_types:                  0
% 7.26/1.50  sat_num_of_epr_types:                   0
% 7.26/1.50  sat_num_of_non_cyclic_types:            0
% 7.26/1.50  sat_guarded_non_collapsed_types:        0
% 7.26/1.50  num_pure_diseq_elim:                    0
% 7.26/1.50  simp_replaced_by:                       0
% 7.26/1.50  res_preprocessed:                       59
% 7.26/1.50  prep_upred:                             0
% 7.26/1.50  prep_unflattend:                        0
% 7.26/1.50  smt_new_axioms:                         0
% 7.26/1.50  pred_elim_cands:                        1
% 7.26/1.50  pred_elim:                              0
% 7.26/1.50  pred_elim_cl:                           0
% 7.26/1.50  pred_elim_cycles:                       1
% 7.26/1.50  merged_defs:                            6
% 7.26/1.50  merged_defs_ncl:                        0
% 7.26/1.50  bin_hyper_res:                          6
% 7.26/1.50  prep_cycles:                            3
% 7.26/1.50  pred_elim_time:                         0.
% 7.26/1.50  splitting_time:                         0.
% 7.26/1.50  sem_filter_time:                        0.
% 7.26/1.50  monotx_time:                            0.
% 7.26/1.50  subtype_inf_time:                       0.
% 7.26/1.50  
% 7.26/1.50  ------ Problem properties
% 7.26/1.50  
% 7.26/1.50  clauses:                                16
% 7.26/1.50  conjectures:                            4
% 7.26/1.50  epr:                                    4
% 7.26/1.50  horn:                                   16
% 7.26/1.50  ground:                                 4
% 7.26/1.50  unary:                                  13
% 7.26/1.50  binary:                                 3
% 7.26/1.50  lits:                                   19
% 7.26/1.50  lits_eq:                                13
% 7.26/1.50  fd_pure:                                0
% 7.26/1.50  fd_pseudo:                              0
% 7.26/1.50  fd_cond:                                0
% 7.26/1.50  fd_pseudo_cond:                         0
% 7.26/1.50  ac_symbols:                             1
% 7.26/1.50  
% 7.26/1.50  ------ Propositional Solver
% 7.26/1.50  
% 7.26/1.50  prop_solver_calls:                      28
% 7.26/1.50  prop_fast_solver_calls:                 330
% 7.26/1.50  smt_solver_calls:                       0
% 7.26/1.50  smt_fast_solver_calls:                  0
% 7.26/1.50  prop_num_of_clauses:                    7155
% 7.26/1.50  prop_preprocess_simplified:             8470
% 7.26/1.50  prop_fo_subsumed:                       0
% 7.26/1.50  prop_solver_time:                       0.
% 7.26/1.50  smt_solver_time:                        0.
% 7.26/1.50  smt_fast_solver_time:                   0.
% 7.26/1.50  prop_fast_solver_time:                  0.
% 7.26/1.50  prop_unsat_core_time:                   0.
% 7.26/1.50  
% 7.26/1.50  ------ QBF
% 7.26/1.50  
% 7.26/1.50  qbf_q_res:                              0
% 7.26/1.50  qbf_num_tautologies:                    0
% 7.26/1.50  qbf_prep_cycles:                        0
% 7.26/1.50  
% 7.26/1.50  ------ BMC1
% 7.26/1.50  
% 7.26/1.50  bmc1_current_bound:                     -1
% 7.26/1.50  bmc1_last_solved_bound:                 -1
% 7.26/1.50  bmc1_unsat_core_size:                   -1
% 7.26/1.50  bmc1_unsat_core_parents_size:           -1
% 7.26/1.50  bmc1_merge_next_fun:                    0
% 7.26/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.26/1.50  
% 7.26/1.50  ------ Instantiation
% 7.26/1.50  
% 7.26/1.50  inst_num_of_clauses:                    2493
% 7.26/1.50  inst_num_in_passive:                    889
% 7.26/1.50  inst_num_in_active:                     648
% 7.26/1.50  inst_num_in_unprocessed:                956
% 7.26/1.50  inst_num_of_loops:                      740
% 7.26/1.50  inst_num_of_learning_restarts:          0
% 7.26/1.50  inst_num_moves_active_passive:          86
% 7.26/1.50  inst_lit_activity:                      0
% 7.26/1.50  inst_lit_activity_moves:                1
% 7.26/1.50  inst_num_tautologies:                   0
% 7.26/1.50  inst_num_prop_implied:                  0
% 7.26/1.50  inst_num_existing_simplified:           0
% 7.26/1.50  inst_num_eq_res_simplified:             0
% 7.26/1.50  inst_num_child_elim:                    0
% 7.26/1.50  inst_num_of_dismatching_blockings:      1454
% 7.26/1.50  inst_num_of_non_proper_insts:           1145
% 7.26/1.50  inst_num_of_duplicates:                 0
% 7.26/1.50  inst_inst_num_from_inst_to_res:         0
% 7.26/1.50  inst_dismatching_checking_time:         0.
% 7.26/1.50  
% 7.26/1.50  ------ Resolution
% 7.26/1.50  
% 7.26/1.50  res_num_of_clauses:                     0
% 7.26/1.50  res_num_in_passive:                     0
% 7.26/1.50  res_num_in_active:                      0
% 7.26/1.50  res_num_of_loops:                       62
% 7.26/1.50  res_forward_subset_subsumed:            1710
% 7.26/1.50  res_backward_subset_subsumed:           0
% 7.26/1.50  res_forward_subsumed:                   0
% 7.26/1.50  res_backward_subsumed:                  0
% 7.26/1.50  res_forward_subsumption_resolution:     0
% 7.26/1.50  res_backward_subsumption_resolution:    0
% 7.26/1.50  res_clause_to_clause_subsumption:       20424
% 7.26/1.50  res_orphan_elimination:                 0
% 7.26/1.50  res_tautology_del:                      188
% 7.26/1.50  res_num_eq_res_simplified:              0
% 7.26/1.50  res_num_sel_changes:                    0
% 7.26/1.50  res_moves_from_active_to_pass:          0
% 7.26/1.50  
% 7.26/1.50  ------ Superposition
% 7.26/1.50  
% 7.26/1.50  sup_time_total:                         0.
% 7.26/1.50  sup_time_generating:                    0.
% 7.26/1.50  sup_time_sim_full:                      0.
% 7.26/1.50  sup_time_sim_immed:                     0.
% 7.26/1.50  
% 7.26/1.50  sup_num_of_clauses:                     1652
% 7.26/1.50  sup_num_in_active:                      119
% 7.26/1.50  sup_num_in_passive:                     1533
% 7.26/1.50  sup_num_of_loops:                       146
% 7.26/1.50  sup_fw_superposition:                   2451
% 7.26/1.50  sup_bw_superposition:                   2292
% 7.26/1.50  sup_immediate_simplified:               1835
% 7.26/1.50  sup_given_eliminated:                   10
% 7.26/1.50  comparisons_done:                       0
% 7.26/1.50  comparisons_avoided:                    0
% 7.26/1.50  
% 7.26/1.50  ------ Simplifications
% 7.26/1.50  
% 7.26/1.50  
% 7.26/1.50  sim_fw_subset_subsumed:                 4
% 7.26/1.50  sim_bw_subset_subsumed:                 0
% 7.26/1.50  sim_fw_subsumed:                        333
% 7.26/1.50  sim_bw_subsumed:                        24
% 7.26/1.50  sim_fw_subsumption_res:                 0
% 7.26/1.50  sim_bw_subsumption_res:                 0
% 7.26/1.50  sim_tautology_del:                      0
% 7.26/1.50  sim_eq_tautology_del:                   227
% 7.26/1.50  sim_eq_res_simp:                        3
% 7.26/1.50  sim_fw_demodulated:                     773
% 7.26/1.50  sim_bw_demodulated:                     118
% 7.26/1.50  sim_light_normalised:                   770
% 7.26/1.50  sim_joinable_taut:                      84
% 7.26/1.50  sim_joinable_simp:                      0
% 7.26/1.50  sim_ac_normalised:                      0
% 7.26/1.50  sim_smt_subsumption:                    0
% 7.26/1.50  
%------------------------------------------------------------------------------
