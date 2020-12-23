%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:17 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 308 expanded)
%              Number of clauses        :   46 ( 113 expanded)
%              Number of leaves         :   10 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  119 ( 563 expanded)
%              Number of equality atoms :   68 ( 232 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f21])).

fof(f34,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f32])).

fof(f36,plain,(
    ~ r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_368,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_371,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_863,plain,
    ( k2_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_368,c_371])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_630,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_369,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_374,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1018,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_369,c_374])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_375,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1343,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1018,c_375])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1535,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK2)) = sK3 ),
    inference(superposition,[status(thm)],[c_1343,c_9])).

cnf(c_2202,plain,
    ( k4_xboole_0(sK3,sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_630,c_1535])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4841,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2202,c_8])).

cnf(c_5679,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4841])).

cnf(c_5745,plain,
    ( k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_863,c_5679])).

cnf(c_5785,plain,
    ( k4_xboole_0(sK3,sK1) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_5745,c_2202])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_376,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6142,plain,
    ( k4_xboole_0(sK3,sK3) != k1_xboole_0
    | r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5785,c_376])).

cnf(c_724,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_0])).

cnf(c_1534,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK2),k1_xboole_0) = sK3 ),
    inference(superposition,[status(thm)],[c_1343,c_724])).

cnf(c_1532,plain,
    ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1343,c_8])).

cnf(c_3692,plain,
    ( k4_xboole_0(sK3,sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1534,c_1532])).

cnf(c_1023,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_369,c_375])).

cnf(c_1355,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_1023,c_724])).

cnf(c_1707,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_1355,c_7])).

cnf(c_2029,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1707,c_1023])).

cnf(c_2462,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2029,c_8])).

cnf(c_2609,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_2462])).

cnf(c_2633,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2609,c_2029])).

cnf(c_3721,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3692,c_2633])).

cnf(c_6161,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6142,c_3721])).

cnf(c_6162,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6161])).

cnf(c_1857,plain,
    ( ~ r1_xboole_0(sK3,sK1)
    | r1_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1858,plain,
    ( r1_xboole_0(sK3,sK1) != iProver_top
    | r1_xboole_0(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1857])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,plain,
    ( r1_xboole_0(sK1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6162,c_1858,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:06:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.61/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.99  
% 3.61/0.99  ------  iProver source info
% 3.61/0.99  
% 3.61/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.99  git: non_committed_changes: false
% 3.61/0.99  git: last_make_outside_of_git: false
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  ------ Parsing...
% 3.61/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.99  ------ Proving...
% 3.61/0.99  ------ Problem Properties 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  clauses                                 13
% 3.61/0.99  conjectures                             3
% 3.61/0.99  EPR                                     4
% 3.61/0.99  Horn                                    12
% 3.61/0.99  unary                                   7
% 3.61/0.99  binary                                  6
% 3.61/0.99  lits                                    19
% 3.61/0.99  lits eq                                 7
% 3.61/0.99  fd_pure                                 0
% 3.61/0.99  fd_pseudo                               0
% 3.61/0.99  fd_cond                                 0
% 3.61/0.99  fd_pseudo_cond                          0
% 3.61/0.99  AC symbols                              0
% 3.61/0.99  
% 3.61/0.99  ------ Input Options Time Limit: Unbounded
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  Current options:
% 3.61/0.99  ------ 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ Proving...
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS status Theorem for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  fof(f10,conjecture,(
% 3.61/0.99    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f11,negated_conjecture,(
% 3.61/0.99    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.61/0.99    inference(negated_conjecture,[],[f10])).
% 3.61/0.99  
% 3.61/0.99  fof(f16,plain,(
% 3.61/0.99    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 3.61/0.99    inference(ennf_transformation,[],[f11])).
% 3.61/0.99  
% 3.61/0.99  fof(f17,plain,(
% 3.61/0.99    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 3.61/0.99    inference(flattening,[],[f16])).
% 3.61/0.99  
% 3.61/0.99  fof(f21,plain,(
% 3.61/0.99    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK1,sK3) & r1_xboole_0(sK2,sK3) & r1_tarski(sK1,sK2))),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f22,plain,(
% 3.61/0.99    ~r1_xboole_0(sK1,sK3) & r1_xboole_0(sK2,sK3) & r1_tarski(sK1,sK2)),
% 3.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f21])).
% 3.61/0.99  
% 3.61/0.99  fof(f34,plain,(
% 3.61/0.99    r1_tarski(sK1,sK2)),
% 3.61/0.99    inference(cnf_transformation,[],[f22])).
% 3.61/0.99  
% 3.61/0.99  fof(f5,axiom,(
% 3.61/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f15,plain,(
% 3.61/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.61/0.99    inference(ennf_transformation,[],[f5])).
% 3.61/0.99  
% 3.61/0.99  fof(f29,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f15])).
% 3.61/0.99  
% 3.61/0.99  fof(f1,axiom,(
% 3.61/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f23,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f1])).
% 3.61/0.99  
% 3.61/0.99  fof(f6,axiom,(
% 3.61/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f30,plain,(
% 3.61/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.61/0.99    inference(cnf_transformation,[],[f6])).
% 3.61/0.99  
% 3.61/0.99  fof(f35,plain,(
% 3.61/0.99    r1_xboole_0(sK2,sK3)),
% 3.61/0.99    inference(cnf_transformation,[],[f22])).
% 3.61/0.99  
% 3.61/0.99  fof(f3,axiom,(
% 3.61/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f13,plain,(
% 3.61/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.61/0.99    inference(ennf_transformation,[],[f3])).
% 3.61/0.99  
% 3.61/0.99  fof(f26,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f13])).
% 3.61/0.99  
% 3.61/0.99  fof(f2,axiom,(
% 3.61/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f18,plain,(
% 3.61/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.61/0.99    inference(nnf_transformation,[],[f2])).
% 3.61/0.99  
% 3.61/0.99  fof(f24,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f18])).
% 3.61/0.99  
% 3.61/0.99  fof(f8,axiom,(
% 3.61/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f32,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f8])).
% 3.61/0.99  
% 3.61/0.99  fof(f38,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.61/0.99    inference(definition_unfolding,[],[f24,f32])).
% 3.61/0.99  
% 3.61/0.99  fof(f9,axiom,(
% 3.61/0.99    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f33,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.61/0.99    inference(cnf_transformation,[],[f9])).
% 3.61/0.99  
% 3.61/0.99  fof(f41,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 3.61/0.99    inference(definition_unfolding,[],[f33,f32])).
% 3.61/0.99  
% 3.61/0.99  fof(f7,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.61/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f31,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f7])).
% 3.61/0.99  
% 3.61/0.99  fof(f25,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.61/0.99    inference(cnf_transformation,[],[f18])).
% 3.61/0.99  
% 3.61/0.99  fof(f37,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.61/0.99    inference(definition_unfolding,[],[f25,f32])).
% 3.61/0.99  
% 3.61/0.99  fof(f36,plain,(
% 3.61/0.99    ~r1_xboole_0(sK1,sK3)),
% 3.61/0.99    inference(cnf_transformation,[],[f22])).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12,negated_conjecture,
% 3.61/0.99      ( r1_tarski(sK1,sK2) ),
% 3.61/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_368,plain,
% 3.61/0.99      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.61/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_371,plain,
% 3.61/0.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_863,plain,
% 3.61/0.99      ( k2_xboole_0(sK1,sK2) = sK2 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_368,c_371]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_0,plain,
% 3.61/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7,plain,
% 3.61/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_630,plain,
% 3.61/0.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11,negated_conjecture,
% 3.61/0.99      ( r1_xboole_0(sK2,sK3) ),
% 3.61/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_369,plain,
% 3.61/0.99      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_374,plain,
% 3.61/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.61/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1018,plain,
% 3.61/0.99      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_369,c_374]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2,plain,
% 3.61/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.61/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_375,plain,
% 3.61/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 3.61/0.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1343,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,k4_xboole_0(sK3,sK2)) = k1_xboole_0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1018,c_375]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9,plain,
% 3.61/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1535,plain,
% 3.61/0.99      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK2)) = sK3 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1343,c_9]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2202,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,sK2) = sK3 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_630,c_1535]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8,plain,
% 3.61/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4841,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,X0) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2202,c_8]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5679,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,k2_xboole_0(X0,sK2)) = k4_xboole_0(sK3,X0) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_0,c_4841]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5745,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_863,c_5679]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5785,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,sK1) = sK3 ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_5745,c_2202]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1,plain,
% 3.61/0.99      ( r1_xboole_0(X0,X1)
% 3.61/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_376,plain,
% 3.61/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.61/0.99      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6142,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,sK3) != k1_xboole_0
% 3.61/0.99      | r1_xboole_0(sK3,sK1) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5785,c_376]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_724,plain,
% 3.61/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_9,c_0]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1534,plain,
% 3.61/0.99      ( k2_xboole_0(k4_xboole_0(sK3,sK2),k1_xboole_0) = sK3 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1343,c_724]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1532,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK2),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1343,c_8]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3692,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,sK3) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1534,c_1532]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1023,plain,
% 3.61/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_369,c_375]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1355,plain,
% 3.61/0.99      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = sK2 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1023,c_724]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1707,plain,
% 3.61/0.99      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_1355,c_7]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2029,plain,
% 3.61/0.99      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_1707,c_1023]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2462,plain,
% 3.61/0.99      ( k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_2029,c_8]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2609,plain,
% 3.61/0.99      ( k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_7,c_2462]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2633,plain,
% 3.61/0.99      ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_2609,c_2029]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3721,plain,
% 3.61/0.99      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_3692,c_2633]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6161,plain,
% 3.61/0.99      ( k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,sK1) = iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_6142,c_3721]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6162,plain,
% 3.61/0.99      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 3.61/0.99      inference(equality_resolution_simp,[status(thm)],[c_6161]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1857,plain,
% 3.61/0.99      ( ~ r1_xboole_0(sK3,sK1) | r1_xboole_0(sK1,sK3) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1858,plain,
% 3.61/0.99      ( r1_xboole_0(sK3,sK1) != iProver_top
% 3.61/0.99      | r1_xboole_0(sK1,sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_1857]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10,negated_conjecture,
% 3.61/0.99      ( ~ r1_xboole_0(sK1,sK3) ),
% 3.61/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_15,plain,
% 3.61/0.99      ( r1_xboole_0(sK1,sK3) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(contradiction,plain,
% 3.61/0.99      ( $false ),
% 3.61/0.99      inference(minisat,[status(thm)],[c_6162,c_1858,c_15]) ).
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  ------                               Statistics
% 3.61/0.99  
% 3.61/0.99  ------ Selected
% 3.61/0.99  
% 3.61/0.99  total_time:                             0.196
% 3.61/0.99  
%------------------------------------------------------------------------------
