%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:43 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 384 expanded)
%              Number of clauses        :   49 ( 156 expanded)
%              Number of leaves         :   12 (  95 expanded)
%              Depth                    :   20
%              Number of atoms          :  117 ( 634 expanded)
%              Number of equality atoms :   92 ( 469 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK0 != sK2
      & r1_xboole_0(sK2,sK1)
      & r1_xboole_0(sK0,sK1)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( sK0 != sK2
    & r1_xboole_0(sK2,sK1)
    & r1_xboole_0(sK0,sK1)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f27,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_10,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_307,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_10,c_5])).

cnf(c_318,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_307,c_5])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_602,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_318,c_3])).

cnf(c_604,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_602,c_3])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_80,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_4])).

cnf(c_442,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_80])).

cnf(c_444,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_442,c_3])).

cnf(c_1031,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_604,c_444])).

cnf(c_441,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_3])).

cnf(c_28588,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK2,sK1)) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1031,c_441])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_48,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_49,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_48])).

cnf(c_203,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_49,c_3])).

cnf(c_298,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_0,c_203])).

cnf(c_1730,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_298,c_318])).

cnf(c_309,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_315,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_309,c_4])).

cnf(c_1731,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1730,c_315])).

cnf(c_306,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_2642,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_1731,c_306])).

cnf(c_2765,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_2642,c_6])).

cnf(c_2766,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(light_normalisation,[status(thm)],[c_2765,c_604])).

cnf(c_2767,plain,
    ( k4_xboole_0(sK0,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_2766,c_4,c_315,c_444])).

cnf(c_2810,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_2767,c_318])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_53,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_54,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_53])).

cnf(c_204,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_54,c_3])).

cnf(c_676,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_204,c_315])).

cnf(c_678,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_0,c_676])).

cnf(c_2995,plain,
    ( k2_xboole_0(sK0,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_678,c_2767])).

cnf(c_28595,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_28588,c_2810,c_2995])).

cnf(c_28596,plain,
    ( sK2 = sK0 ),
    inference(demodulation,[status(thm)],[c_28595,c_315])).

cnf(c_64,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_108,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_65,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_105,plain,
    ( sK2 != X0
    | sK0 != X0
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_107,plain,
    ( sK2 != sK0
    | sK0 = sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_7,negated_conjecture,
    ( sK0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28596,c_108,c_107,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:29:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.75/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/1.51  
% 7.75/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.51  
% 7.75/1.51  ------  iProver source info
% 7.75/1.51  
% 7.75/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.51  git: non_committed_changes: false
% 7.75/1.51  git: last_make_outside_of_git: false
% 7.75/1.51  
% 7.75/1.51  ------ 
% 7.75/1.51  ------ Parsing...
% 7.75/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.51  
% 7.75/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.75/1.51  
% 7.75/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.51  
% 7.75/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.75/1.51  ------ Proving...
% 7.75/1.51  ------ Problem Properties 
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  clauses                                 10
% 7.75/1.51  conjectures                             2
% 7.75/1.51  EPR                                     1
% 7.75/1.51  Horn                                    10
% 7.75/1.51  unary                                   10
% 7.75/1.51  binary                                  0
% 7.75/1.51  lits                                    10
% 7.75/1.51  lits eq                                 10
% 7.75/1.51  fd_pure                                 0
% 7.75/1.51  fd_pseudo                               0
% 7.75/1.51  fd_cond                                 0
% 7.75/1.51  fd_pseudo_cond                          0
% 7.75/1.51  AC symbols                              0
% 7.75/1.51  
% 7.75/1.51  ------ Input Options Time Limit: Unbounded
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  ------ 
% 7.75/1.51  Current options:
% 7.75/1.51  ------ 
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  ------ Proving...
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  % SZS status Theorem for theBenchmark.p
% 7.75/1.51  
% 7.75/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.51  
% 7.75/1.51  fof(f9,conjecture,(
% 7.75/1.51    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f10,negated_conjecture,(
% 7.75/1.51    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 7.75/1.51    inference(negated_conjecture,[],[f9])).
% 7.75/1.51  
% 7.75/1.51  fof(f13,plain,(
% 7.75/1.51    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 7.75/1.51    inference(ennf_transformation,[],[f10])).
% 7.75/1.51  
% 7.75/1.51  fof(f14,plain,(
% 7.75/1.51    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 7.75/1.51    inference(flattening,[],[f13])).
% 7.75/1.51  
% 7.75/1.51  fof(f15,plain,(
% 7.75/1.51    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1))),
% 7.75/1.51    introduced(choice_axiom,[])).
% 7.75/1.51  
% 7.75/1.51  fof(f16,plain,(
% 7.75/1.51    sK0 != sK2 & r1_xboole_0(sK2,sK1) & r1_xboole_0(sK0,sK1) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 7.75/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 7.75/1.51  
% 7.75/1.51  fof(f25,plain,(
% 7.75/1.51    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1)),
% 7.75/1.51    inference(cnf_transformation,[],[f16])).
% 7.75/1.51  
% 7.75/1.51  fof(f6,axiom,(
% 7.75/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f22,plain,(
% 7.75/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f6])).
% 7.75/1.51  
% 7.75/1.51  fof(f4,axiom,(
% 7.75/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f20,plain,(
% 7.75/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.75/1.51    inference(cnf_transformation,[],[f4])).
% 7.75/1.51  
% 7.75/1.51  fof(f7,axiom,(
% 7.75/1.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f23,plain,(
% 7.75/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f7])).
% 7.75/1.51  
% 7.75/1.51  fof(f3,axiom,(
% 7.75/1.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f19,plain,(
% 7.75/1.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.75/1.51    inference(cnf_transformation,[],[f3])).
% 7.75/1.51  
% 7.75/1.51  fof(f8,axiom,(
% 7.75/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f24,plain,(
% 7.75/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.75/1.51    inference(cnf_transformation,[],[f8])).
% 7.75/1.51  
% 7.75/1.51  fof(f30,plain,(
% 7.75/1.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.75/1.51    inference(definition_unfolding,[],[f19,f24])).
% 7.75/1.51  
% 7.75/1.51  fof(f5,axiom,(
% 7.75/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f21,plain,(
% 7.75/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.75/1.51    inference(cnf_transformation,[],[f5])).
% 7.75/1.51  
% 7.75/1.51  fof(f1,axiom,(
% 7.75/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f17,plain,(
% 7.75/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f1])).
% 7.75/1.51  
% 7.75/1.51  fof(f2,axiom,(
% 7.75/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.75/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.51  
% 7.75/1.51  fof(f11,plain,(
% 7.75/1.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.75/1.51    inference(unused_predicate_definition_removal,[],[f2])).
% 7.75/1.51  
% 7.75/1.51  fof(f12,plain,(
% 7.75/1.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 7.75/1.51    inference(ennf_transformation,[],[f11])).
% 7.75/1.51  
% 7.75/1.51  fof(f18,plain,(
% 7.75/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.75/1.51    inference(cnf_transformation,[],[f12])).
% 7.75/1.51  
% 7.75/1.51  fof(f29,plain,(
% 7.75/1.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.75/1.51    inference(definition_unfolding,[],[f18,f24])).
% 7.75/1.51  
% 7.75/1.51  fof(f27,plain,(
% 7.75/1.51    r1_xboole_0(sK2,sK1)),
% 7.75/1.51    inference(cnf_transformation,[],[f16])).
% 7.75/1.51  
% 7.75/1.51  fof(f26,plain,(
% 7.75/1.51    r1_xboole_0(sK0,sK1)),
% 7.75/1.51    inference(cnf_transformation,[],[f16])).
% 7.75/1.51  
% 7.75/1.51  fof(f28,plain,(
% 7.75/1.51    sK0 != sK2),
% 7.75/1.51    inference(cnf_transformation,[],[f16])).
% 7.75/1.51  
% 7.75/1.51  cnf(c_10,negated_conjecture,
% 7.75/1.51      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f25]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_5,plain,
% 7.75/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f22]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_307,plain,
% 7.75/1.51      ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) = k4_xboole_0(sK2,sK1) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_10,c_5]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_318,plain,
% 7.75/1.51      ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK2,sK1) ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_307,c_5]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_3,plain,
% 7.75/1.51      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f20]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_602,plain,
% 7.75/1.51      ( k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK2) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_318,c_3]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_604,plain,
% 7.75/1.51      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,sK0) ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_602,c_3]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_6,plain,
% 7.75/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.75/1.51      inference(cnf_transformation,[],[f23]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2,plain,
% 7.75/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.75/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_4,plain,
% 7.75/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.75/1.51      inference(cnf_transformation,[],[f21]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_80,plain,
% 7.75/1.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.75/1.51      inference(light_normalisation,[status(thm)],[c_2,c_4]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_442,plain,
% 7.75/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_6,c_80]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_444,plain,
% 7.75/1.51      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_442,c_3]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1031,plain,
% 7.75/1.51      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k1_xboole_0 ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_604,c_444]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_441,plain,
% 7.75/1.51      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_6,c_3]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_28588,plain,
% 7.75/1.51      ( k2_xboole_0(sK0,k4_xboole_0(sK2,sK1)) = k2_xboole_0(sK0,k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1031,c_441]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_0,plain,
% 7.75/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.75/1.51      inference(cnf_transformation,[],[f17]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1,plain,
% 7.75/1.51      ( ~ r1_xboole_0(X0,X1)
% 7.75/1.51      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.75/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_8,negated_conjecture,
% 7.75/1.51      ( r1_xboole_0(sK2,sK1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f27]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_48,plain,
% 7.75/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.75/1.51      | sK1 != X1
% 7.75/1.51      | sK2 != X0 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_49,plain,
% 7.75/1.51      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_48]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_203,plain,
% 7.75/1.51      ( k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_49,c_3]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_298,plain,
% 7.75/1.51      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK1)) = k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_0,c_203]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1730,plain,
% 7.75/1.51      ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
% 7.75/1.51      inference(light_normalisation,[status(thm)],[c_298,c_318]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_309,plain,
% 7.75/1.51      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_315,plain,
% 7.75/1.51      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.75/1.51      inference(light_normalisation,[status(thm)],[c_309,c_4]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_1731,plain,
% 7.75/1.51      ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_1730,c_315]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_306,plain,
% 7.75/1.51      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2642,plain,
% 7.75/1.51      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_1731,c_306]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2765,plain,
% 7.75/1.51      ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) = k4_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_2642,c_6]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2766,plain,
% 7.75/1.51      ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)))) = k4_xboole_0(sK2,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
% 7.75/1.51      inference(light_normalisation,[status(thm)],[c_2765,c_604]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2767,plain,
% 7.75/1.51      ( k4_xboole_0(sK0,sK1) = sK2 ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_2766,c_4,c_315,c_444]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2810,plain,
% 7.75/1.51      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_2767,c_318]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_9,negated_conjecture,
% 7.75/1.51      ( r1_xboole_0(sK0,sK1) ),
% 7.75/1.51      inference(cnf_transformation,[],[f26]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_53,plain,
% 7.75/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.75/1.51      | sK1 != X1
% 7.75/1.51      | sK0 != X0 ),
% 7.75/1.51      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_54,plain,
% 7.75/1.51      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 7.75/1.51      inference(unflattening,[status(thm)],[c_53]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_204,plain,
% 7.75/1.51      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_54,c_3]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_676,plain,
% 7.75/1.51      ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,sK1) ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_204,c_315]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_678,plain,
% 7.75/1.51      ( k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1) ),
% 7.75/1.51      inference(superposition,[status(thm)],[c_0,c_676]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_2995,plain,
% 7.75/1.51      ( k2_xboole_0(sK0,sK2) = sK2 ),
% 7.75/1.51      inference(light_normalisation,[status(thm)],[c_678,c_2767]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_28595,plain,
% 7.75/1.51      ( k2_xboole_0(sK0,k1_xboole_0) = sK2 ),
% 7.75/1.51      inference(light_normalisation,
% 7.75/1.51                [status(thm)],
% 7.75/1.51                [c_28588,c_2810,c_2995]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_28596,plain,
% 7.75/1.51      ( sK2 = sK0 ),
% 7.75/1.51      inference(demodulation,[status(thm)],[c_28595,c_315]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_64,plain,( X0 = X0 ),theory(equality) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_108,plain,
% 7.75/1.51      ( sK0 = sK0 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_64]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_65,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_105,plain,
% 7.75/1.51      ( sK2 != X0 | sK0 != X0 | sK0 = sK2 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_65]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_107,plain,
% 7.75/1.51      ( sK2 != sK0 | sK0 = sK2 | sK0 != sK0 ),
% 7.75/1.51      inference(instantiation,[status(thm)],[c_105]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(c_7,negated_conjecture,
% 7.75/1.51      ( sK0 != sK2 ),
% 7.75/1.51      inference(cnf_transformation,[],[f28]) ).
% 7.75/1.51  
% 7.75/1.51  cnf(contradiction,plain,
% 7.75/1.51      ( $false ),
% 7.75/1.51      inference(minisat,[status(thm)],[c_28596,c_108,c_107,c_7]) ).
% 7.75/1.51  
% 7.75/1.51  
% 7.75/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.51  
% 7.75/1.51  ------                               Statistics
% 7.75/1.51  
% 7.75/1.51  ------ Selected
% 7.75/1.51  
% 7.75/1.51  total_time:                             0.932
% 7.75/1.51  
%------------------------------------------------------------------------------
