%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:37 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 321 expanded)
%              Number of clauses        :   36 (  92 expanded)
%              Number of leaves         :   11 (  94 expanded)
%              Depth                    :   14
%              Number of atoms          :   79 ( 330 expanded)
%              Number of equality atoms :   63 ( 314 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f26,f25,f25])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f25,f25])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f11,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f28,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f25])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_556,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_7,c_2])).

cnf(c_563,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_556,c_7])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_436,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_14834,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(light_normalisation,[status(thm)],[c_563,c_436])).

cnf(c_14835,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_14834,c_436])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_43,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0
    | k5_xboole_0(sK0,sK1) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_9])).

cnf(c_44,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_43])).

cnf(c_75,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))))))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_44,c_7])).

cnf(c_2709,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))))))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_436,c_75])).

cnf(c_2711,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))))))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2709,c_436])).

cnf(c_14838,plain,
    ( k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14835,c_2711])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_62,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4,c_5])).

cnf(c_115,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_62,c_1])).

cnf(c_117,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_115,c_5,c_62])).

cnf(c_0,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_426,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_6])).

cnf(c_558,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_62])).

cnf(c_610,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_426,c_558])).

cnf(c_1152,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_610,c_1])).

cnf(c_114,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_1])).

cnf(c_120,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_114,c_5,c_62])).

cnf(c_1170,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1152,c_120])).

cnf(c_1248,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1170,c_1170])).

cnf(c_2491,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_0,c_1248])).

cnf(c_2567,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2491,c_0])).

cnf(c_5724,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2567,c_436])).

cnf(c_14839,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14838,c_117,c_436,c_5724])).

cnf(c_14840,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_14839])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:04:32 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.62/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.99  
% 3.62/0.99  ------  iProver source info
% 3.62/0.99  
% 3.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.99  git: non_committed_changes: false
% 3.62/0.99  git: last_make_outside_of_git: false
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  ------ Parsing...
% 3.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  ------ Proving...
% 3.62/0.99  ------ Problem Properties 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  clauses                                 9
% 3.62/0.99  conjectures                             0
% 3.62/0.99  EPR                                     0
% 3.62/0.99  Horn                                    9
% 3.62/0.99  unary                                   9
% 3.62/0.99  binary                                  0
% 3.62/0.99  lits                                    9
% 3.62/0.99  lits eq                                 9
% 3.62/0.99  fd_pure                                 0
% 3.62/0.99  fd_pseudo                               0
% 3.62/0.99  fd_cond                                 0
% 3.62/0.99  fd_pseudo_cond                          0
% 3.62/0.99  AC symbols                              0
% 3.62/0.99  
% 3.62/0.99  ------ Input Options Time Limit: Unbounded
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  Current options:
% 3.62/0.99  ------ 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS status Theorem for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99   Resolution empty clause
% 3.62/0.99  
% 3.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  fof(f9,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f26,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f9])).
% 3.62/0.99  
% 3.62/0.99  fof(f8,axiom,(
% 3.62/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f25,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f8])).
% 3.62/0.99  
% 3.62/0.99  fof(f35,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 3.62/0.99    inference(definition_unfolding,[],[f26,f25,f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f1,axiom,(
% 3.62/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f18,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f1])).
% 3.62/0.99  
% 3.62/0.99  fof(f31,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.62/0.99    inference(definition_unfolding,[],[f18,f25,f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f7,axiom,(
% 3.62/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f24,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f7])).
% 3.62/0.99  
% 3.62/0.99  fof(f34,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.62/0.99    inference(definition_unfolding,[],[f24,f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f4,axiom,(
% 3.62/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f21,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f4])).
% 3.62/0.99  
% 3.62/0.99  fof(f30,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 3.62/0.99    inference(definition_unfolding,[],[f21,f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f2,axiom,(
% 3.62/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f13,plain,(
% 3.62/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 => r1_xboole_0(X0,X1))),
% 3.62/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 3.62/0.99  
% 3.62/0.99  fof(f14,plain,(
% 3.62/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 3.62/0.99    inference(ennf_transformation,[],[f13])).
% 3.62/0.99  
% 3.62/0.99  fof(f19,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.62/0.99    inference(cnf_transformation,[],[f14])).
% 3.62/0.99  
% 3.62/0.99  fof(f32,plain,(
% 3.62/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.62/0.99    inference(definition_unfolding,[],[f19,f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f11,conjecture,(
% 3.62/0.99    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f12,negated_conjecture,(
% 3.62/0.99    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.62/0.99    inference(negated_conjecture,[],[f11])).
% 3.62/0.99  
% 3.62/0.99  fof(f15,plain,(
% 3.62/0.99    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 3.62/0.99    inference(ennf_transformation,[],[f12])).
% 3.62/0.99  
% 3.62/0.99  fof(f16,plain,(
% 3.62/0.99    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f17,plain,(
% 3.62/0.99    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 3.62/0.99  
% 3.62/0.99  fof(f28,plain,(
% 3.62/0.99    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 3.62/0.99    inference(cnf_transformation,[],[f17])).
% 3.62/0.99  
% 3.62/0.99  fof(f37,plain,(
% 3.62/0.99    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))),
% 3.62/0.99    inference(definition_unfolding,[],[f28,f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f5,axiom,(
% 3.62/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f22,plain,(
% 3.62/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.62/0.99    inference(cnf_transformation,[],[f5])).
% 3.62/0.99  
% 3.62/0.99  fof(f33,plain,(
% 3.62/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.62/0.99    inference(definition_unfolding,[],[f22,f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f6,axiom,(
% 3.62/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f23,plain,(
% 3.62/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.62/0.99    inference(cnf_transformation,[],[f6])).
% 3.62/0.99  
% 3.62/0.99  fof(f3,axiom,(
% 3.62/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.62/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f20,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.62/0.99    inference(cnf_transformation,[],[f3])).
% 3.62/0.99  
% 3.62/0.99  fof(f29,plain,(
% 3.62/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.62/0.99    inference(definition_unfolding,[],[f20,f25])).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7,plain,
% 3.62/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 3.62/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_556,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_7,c_2]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_563,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_556,c_7]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1,plain,
% 3.62/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_436,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_14834,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_563,c_436]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_14835,plain,
% 3.62/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))))) = k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_14834,c_436]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3,plain,
% 3.62/0.99      ( r1_xboole_0(X0,X1)
% 3.62/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_9,negated_conjecture,
% 3.62/0.99      ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_43,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 3.62/0.99      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0
% 3.62/0.99      | k5_xboole_0(sK0,sK1) != X1 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_9]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_44,plain,
% 3.62/0.99      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))) != k1_xboole_0 ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_43]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_75,plain,
% 3.62/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))))))) != k1_xboole_0 ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_44,c_7]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2709,plain,
% 3.62/0.99      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))))))) != k1_xboole_0 ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_436,c_75]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2711,plain,
% 3.62/0.99      ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k5_xboole_0(sK0,sK1))))))) != k1_xboole_0 ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_2709,c_436]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_14838,plain,
% 3.62/0.99      ( k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k1_xboole_0 ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_14835,c_2711]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.62/0.99      inference(cnf_transformation,[],[f23]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_62,plain,
% 3.62/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_4,c_5]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_115,plain,
% 3.62/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_62,c_1]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_117,plain,
% 3.62/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_115,c_5,c_62]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_0,plain,
% 3.62/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_426,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_2,c_6]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_558,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_7,c_62]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_610,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_426,c_558]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1152,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_610,c_1]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_114,plain,
% 3.62/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_5,c_1]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_120,plain,
% 3.62/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_114,c_5,c_62]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1170,plain,
% 3.62/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_1152,c_120]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1248,plain,
% 3.62/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1170,c_1170]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2491,plain,
% 3.62/0.99      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_0,c_1248]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2567,plain,
% 3.62/0.99      ( k4_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_2491,c_0]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5724,plain,
% 3.62/0.99      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,X1) ),
% 3.62/0.99      inference(light_normalisation,[status(thm)],[c_2567,c_436]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_14839,plain,
% 3.62/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.62/0.99      inference(demodulation,[status(thm)],[c_14838,c_117,c_436,c_5724]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_14840,plain,
% 3.62/0.99      ( $false ),
% 3.62/0.99      inference(equality_resolution_simp,[status(thm)],[c_14839]) ).
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  ------                               Statistics
% 3.62/0.99  
% 3.62/0.99  ------ Selected
% 3.62/0.99  
% 3.62/0.99  total_time:                             0.407
% 3.62/0.99  
%------------------------------------------------------------------------------
