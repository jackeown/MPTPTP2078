%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:22 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 113 expanded)
%              Number of clauses        :   35 (  42 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   16
%              Number of atoms          :  125 ( 168 expanded)
%              Number of equality atoms :   64 ( 101 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
      & r1_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    & r1_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f24])).

fof(f39,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f22])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f33,f37,f37,f37])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f40,plain,(
    k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f40,f37,f37])).

cnf(c_13,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_274,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( r2_xboole_0(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_275,plain,
    ( k1_xboole_0 = X0
    | r2_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_278,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_281,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2891,plain,
    ( r2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_278,c_281])).

cnf(c_47747,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_275,c_2891])).

cnf(c_48942,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_274,c_47747])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_49380,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) ),
    inference(superposition,[status(thm)],[c_48942,c_10])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_276,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_277,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_680,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_276,c_277])).

cnf(c_49382,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_49380,c_6,c_680])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_49442,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(X0,sK3))) ),
    inference(superposition,[status(thm)],[c_49382,c_7])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_387,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_685,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_10,c_387])).

cnf(c_687,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_685,c_387])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_982,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_687,c_8])).

cnf(c_49446,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(X0,sK3))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_49442,c_6,c_982])).

cnf(c_12,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_386,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK4,sK3))) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(demodulation,[status(thm)],[c_0,c_12])).

cnf(c_49866,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(demodulation,[status(thm)],[c_49446,c_386])).

cnf(c_95,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_7493,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49866,c_7493])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:21:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.49/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.49/2.01  
% 11.49/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.49/2.01  
% 11.49/2.01  ------  iProver source info
% 11.49/2.01  
% 11.49/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.49/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.49/2.01  git: non_committed_changes: false
% 11.49/2.01  git: last_make_outside_of_git: false
% 11.49/2.01  
% 11.49/2.01  ------ 
% 11.49/2.01  ------ Parsing...
% 11.49/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.49/2.01  
% 11.49/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.49/2.01  
% 11.49/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.49/2.01  
% 11.49/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.49/2.01  ------ Proving...
% 11.49/2.01  ------ Problem Properties 
% 11.49/2.01  
% 11.49/2.01  
% 11.49/2.01  clauses                                 14
% 11.49/2.01  conjectures                             2
% 11.49/2.01  EPR                                     2
% 11.49/2.01  Horn                                    12
% 11.49/2.01  unary                                   8
% 11.49/2.01  binary                                  6
% 11.49/2.01  lits                                    20
% 11.49/2.01  lits eq                                 8
% 11.49/2.01  fd_pure                                 0
% 11.49/2.01  fd_pseudo                               0
% 11.49/2.01  fd_cond                                 1
% 11.49/2.01  fd_pseudo_cond                          0
% 11.49/2.01  AC symbols                              0
% 11.49/2.01  
% 11.49/2.01  ------ Input Options Time Limit: Unbounded
% 11.49/2.01  
% 11.49/2.01  
% 11.49/2.01  ------ 
% 11.49/2.01  Current options:
% 11.49/2.01  ------ 
% 11.49/2.01  
% 11.49/2.01  
% 11.49/2.01  
% 11.49/2.01  
% 11.49/2.01  ------ Proving...
% 11.49/2.01  
% 11.49/2.01  
% 11.49/2.01  % SZS status Theorem for theBenchmark.p
% 11.49/2.01  
% 11.49/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.49/2.01  
% 11.49/2.01  fof(f12,conjecture,(
% 11.49/2.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 11.49/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.01  
% 11.49/2.01  fof(f13,negated_conjecture,(
% 11.49/2.01    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 11.49/2.01    inference(negated_conjecture,[],[f12])).
% 11.49/2.01  
% 11.49/2.01  fof(f19,plain,(
% 11.49/2.01    ? [X0,X1,X2] : (k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 11.49/2.01    inference(ennf_transformation,[],[f13])).
% 11.49/2.01  
% 11.49/2.01  fof(f24,plain,(
% 11.49/2.01    ? [X0,X1,X2] : (k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) & r1_xboole_0(sK2,sK3))),
% 11.49/2.01    introduced(choice_axiom,[])).
% 11.49/2.01  
% 11.49/2.01  fof(f25,plain,(
% 11.49/2.01    k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) & r1_xboole_0(sK2,sK3)),
% 11.49/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f24])).
% 11.49/2.01  
% 11.49/2.01  fof(f39,plain,(
% 11.49/2.01    r1_xboole_0(sK2,sK3)),
% 11.49/2.01    inference(cnf_transformation,[],[f25])).
% 11.49/2.01  
% 11.49/2.01  fof(f11,axiom,(
% 11.49/2.01    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 11.49/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.01  
% 11.49/2.01  fof(f18,plain,(
% 11.49/2.01    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 11.49/2.01    inference(ennf_transformation,[],[f11])).
% 11.49/2.01  
% 11.49/2.01  fof(f38,plain,(
% 11.49/2.01    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 11.49/2.01    inference(cnf_transformation,[],[f18])).
% 11.49/2.01  
% 11.49/2.01  fof(f3,axiom,(
% 11.49/2.01    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 11.49/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.01  
% 11.49/2.01  fof(f16,plain,(
% 11.49/2.01    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 11.49/2.01    inference(ennf_transformation,[],[f3])).
% 11.49/2.01  
% 11.49/2.01  fof(f22,plain,(
% 11.49/2.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1)))),
% 11.49/2.01    introduced(choice_axiom,[])).
% 11.49/2.01  
% 11.49/2.01  fof(f23,plain,(
% 11.49/2.01    ! [X0,X1] : ((~r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 11.49/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f22])).
% 11.49/2.01  
% 11.49/2.01  fof(f29,plain,(
% 11.49/2.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 11.49/2.01    inference(cnf_transformation,[],[f23])).
% 11.49/2.01  
% 11.49/2.01  fof(f2,axiom,(
% 11.49/2.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.49/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.01  
% 11.49/2.01  fof(f14,plain,(
% 11.49/2.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 11.49/2.01    inference(rectify,[],[f2])).
% 11.49/2.01  
% 11.49/2.01  fof(f15,plain,(
% 11.49/2.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.49/2.01    inference(ennf_transformation,[],[f14])).
% 11.49/2.01  
% 11.49/2.01  fof(f20,plain,(
% 11.49/2.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 11.49/2.01    introduced(choice_axiom,[])).
% 11.49/2.01  
% 11.49/2.01  fof(f21,plain,(
% 11.49/2.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 11.49/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f20])).
% 11.49/2.01  
% 11.49/2.01  fof(f28,plain,(
% 11.49/2.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 11.49/2.01    inference(cnf_transformation,[],[f21])).
% 11.49/2.01  
% 11.49/2.01  fof(f10,axiom,(
% 11.49/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.49/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.01  
% 11.49/2.01  fof(f37,plain,(
% 11.49/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.49/2.01    inference(cnf_transformation,[],[f10])).
% 11.49/2.02  
% 11.49/2.02  fof(f41,plain,(
% 11.49/2.02    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.49/2.02    inference(definition_unfolding,[],[f28,f37])).
% 11.49/2.02  
% 11.49/2.02  fof(f9,axiom,(
% 11.49/2.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.49/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f36,plain,(
% 11.49/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.49/2.02    inference(cnf_transformation,[],[f9])).
% 11.49/2.02  
% 11.49/2.02  fof(f5,axiom,(
% 11.49/2.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.49/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f32,plain,(
% 11.49/2.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.49/2.02    inference(cnf_transformation,[],[f5])).
% 11.49/2.02  
% 11.49/2.02  fof(f8,axiom,(
% 11.49/2.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.49/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f35,plain,(
% 11.49/2.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.49/2.02    inference(cnf_transformation,[],[f8])).
% 11.49/2.02  
% 11.49/2.02  fof(f4,axiom,(
% 11.49/2.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.49/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f17,plain,(
% 11.49/2.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.49/2.02    inference(ennf_transformation,[],[f4])).
% 11.49/2.02  
% 11.49/2.02  fof(f31,plain,(
% 11.49/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.49/2.02    inference(cnf_transformation,[],[f17])).
% 11.49/2.02  
% 11.49/2.02  fof(f6,axiom,(
% 11.49/2.02    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 11.49/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f33,plain,(
% 11.49/2.02    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 11.49/2.02    inference(cnf_transformation,[],[f6])).
% 11.49/2.02  
% 11.49/2.02  fof(f43,plain,(
% 11.49/2.02    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 11.49/2.02    inference(definition_unfolding,[],[f33,f37,f37,f37])).
% 11.49/2.02  
% 11.49/2.02  fof(f1,axiom,(
% 11.49/2.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.49/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f26,plain,(
% 11.49/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.49/2.02    inference(cnf_transformation,[],[f1])).
% 11.49/2.02  
% 11.49/2.02  fof(f7,axiom,(
% 11.49/2.02    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 11.49/2.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f34,plain,(
% 11.49/2.02    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 11.49/2.02    inference(cnf_transformation,[],[f7])).
% 11.49/2.02  
% 11.49/2.02  fof(f44,plain,(
% 11.49/2.02    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 11.49/2.02    inference(definition_unfolding,[],[f34,f37])).
% 11.49/2.02  
% 11.49/2.02  fof(f40,plain,(
% 11.49/2.02    k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),
% 11.49/2.02    inference(cnf_transformation,[],[f25])).
% 11.49/2.02  
% 11.49/2.02  fof(f45,plain,(
% 11.49/2.02    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))),
% 11.49/2.02    inference(definition_unfolding,[],[f40,f37,f37])).
% 11.49/2.02  
% 11.49/2.02  cnf(c_13,negated_conjecture,
% 11.49/2.02      ( r1_xboole_0(sK2,sK3) ),
% 11.49/2.02      inference(cnf_transformation,[],[f39]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_274,plain,
% 11.49/2.02      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 11.49/2.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_11,plain,
% 11.49/2.02      ( r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0 ),
% 11.49/2.02      inference(cnf_transformation,[],[f38]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_275,plain,
% 11.49/2.02      ( k1_xboole_0 = X0 | r2_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 11.49/2.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_4,plain,
% 11.49/2.02      ( ~ r2_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 11.49/2.02      inference(cnf_transformation,[],[f29]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_278,plain,
% 11.49/2.02      ( r2_xboole_0(X0,X1) != iProver_top
% 11.49/2.02      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 11.49/2.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_1,plain,
% 11.49/2.02      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 11.49/2.02      | ~ r1_xboole_0(X1,X2) ),
% 11.49/2.02      inference(cnf_transformation,[],[f41]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_281,plain,
% 11.49/2.02      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 11.49/2.02      | r1_xboole_0(X1,X2) != iProver_top ),
% 11.49/2.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_2891,plain,
% 11.49/2.02      ( r2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 11.49/2.02      | r1_xboole_0(X1,X2) != iProver_top ),
% 11.49/2.02      inference(superposition,[status(thm)],[c_278,c_281]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_47747,plain,
% 11.49/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 11.49/2.02      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.49/2.02      inference(superposition,[status(thm)],[c_275,c_2891]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_48942,plain,
% 11.49/2.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 11.49/2.02      inference(superposition,[status(thm)],[c_274,c_47747]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_10,plain,
% 11.49/2.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.49/2.02      inference(cnf_transformation,[],[f36]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_49380,plain,
% 11.49/2.02      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) ),
% 11.49/2.02      inference(superposition,[status(thm)],[c_48942,c_10]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_6,plain,
% 11.49/2.02      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.49/2.02      inference(cnf_transformation,[],[f32]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_9,plain,
% 11.49/2.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.49/2.02      inference(cnf_transformation,[],[f35]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_276,plain,
% 11.49/2.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.49/2.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_5,plain,
% 11.49/2.02      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.49/2.02      inference(cnf_transformation,[],[f31]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_277,plain,
% 11.49/2.02      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.49/2.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_680,plain,
% 11.49/2.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 11.49/2.02      inference(superposition,[status(thm)],[c_276,c_277]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_49382,plain,
% 11.49/2.02      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 11.49/2.02      inference(demodulation,[status(thm)],[c_49380,c_6,c_680]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_7,plain,
% 11.49/2.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
% 11.49/2.02      inference(cnf_transformation,[],[f43]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_49442,plain,
% 11.49/2.02      ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),k4_xboole_0(sK2,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(X0,sK3))) ),
% 11.49/2.02      inference(superposition,[status(thm)],[c_49382,c_7]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_0,plain,
% 11.49/2.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.49/2.02      inference(cnf_transformation,[],[f26]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_387,plain,
% 11.49/2.02      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.49/2.02      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_685,plain,
% 11.49/2.02      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
% 11.49/2.02      inference(superposition,[status(thm)],[c_10,c_387]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_687,plain,
% 11.49/2.02      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.49/2.02      inference(light_normalisation,[status(thm)],[c_685,c_387]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_8,plain,
% 11.49/2.02      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 11.49/2.02      inference(cnf_transformation,[],[f44]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_982,plain,
% 11.49/2.02      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.49/2.02      inference(demodulation,[status(thm)],[c_687,c_8]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_49446,plain,
% 11.49/2.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(X0,sK3))) = k4_xboole_0(sK2,k4_xboole_0(sK2,X0)) ),
% 11.49/2.02      inference(demodulation,[status(thm)],[c_49442,c_6,c_982]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_12,negated_conjecture,
% 11.49/2.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))) ),
% 11.49/2.02      inference(cnf_transformation,[],[f45]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_386,plain,
% 11.49/2.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK4,sK3))) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 11.49/2.02      inference(demodulation,[status(thm)],[c_0,c_12]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_49866,plain,
% 11.49/2.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 11.49/2.02      inference(demodulation,[status(thm)],[c_49446,c_386]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_95,plain,( X0 = X0 ),theory(equality) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_7493,plain,
% 11.49/2.02      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) ),
% 11.49/2.02      inference(instantiation,[status(thm)],[c_95]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(contradiction,plain,
% 11.49/2.02      ( $false ),
% 11.49/2.02      inference(minisat,[status(thm)],[c_49866,c_7493]) ).
% 11.49/2.02  
% 11.49/2.02  
% 11.49/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.49/2.02  
% 11.49/2.02  ------                               Statistics
% 11.49/2.02  
% 11.49/2.02  ------ Selected
% 11.49/2.02  
% 11.49/2.02  total_time:                             1.093
% 11.49/2.02  
%------------------------------------------------------------------------------
