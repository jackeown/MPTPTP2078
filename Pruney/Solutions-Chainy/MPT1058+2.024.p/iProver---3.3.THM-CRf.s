%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:16 EST 2020

% Result     : Theorem 7.22s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 122 expanded)
%              Number of clauses        :   32 (  33 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  130 ( 216 expanded)
%              Number of equality atoms :   70 ( 120 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

fof(f39,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f37,f28])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f43,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f42,f42])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f28,f42])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_255,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_250,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_256,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1148,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,sK2)) != iProver_top
    | r1_tarski(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_250,c_256])).

cnf(c_1589,plain,
    ( r1_tarski(k4_xboole_0(k10_relat_1(sK0,sK2),X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_255,c_1148])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_252,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_254,plain,
    ( k1_xboole_0 = X0
    | r1_xboole_0(X0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_615,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_252,c_254])).

cnf(c_2285,plain,
    ( k4_xboole_0(k10_relat_1(sK0,sK2),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1589,c_615])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_249,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_251,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2698,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(superposition,[status(thm)],[c_249,c_251])).

cnf(c_6,plain,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_688,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_7])).

cnf(c_734,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_688,c_7])).

cnf(c_2911,plain,
    ( k4_xboole_0(k10_relat_1(sK0,X0),k4_xboole_0(k10_relat_1(sK0,X0),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2698,c_734])).

cnf(c_32063,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2285,c_2911])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_32068,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_32063,c_2])).

cnf(c_9,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_32386,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(demodulation,[status(thm)],[c_32068,c_9])).

cnf(c_85,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_563,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32386,c_563])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n022.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 16:51:56 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 7.22/1.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.22/1.47  
% 7.22/1.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.22/1.47  
% 7.22/1.47  ------  iProver source info
% 7.22/1.47  
% 7.22/1.47  git: date: 2020-06-30 10:37:57 +0100
% 7.22/1.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.22/1.47  git: non_committed_changes: false
% 7.22/1.47  git: last_make_outside_of_git: false
% 7.22/1.47  
% 7.22/1.47  ------ 
% 7.22/1.47  ------ Parsing...
% 7.22/1.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.22/1.47  
% 7.22/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.22/1.47  
% 7.22/1.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.22/1.47  
% 7.22/1.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.22/1.47  ------ Proving...
% 7.22/1.47  ------ Problem Properties 
% 7.22/1.47  
% 7.22/1.47  
% 7.22/1.47  clauses                                 12
% 7.22/1.47  conjectures                             3
% 7.22/1.47  EPR                                     4
% 7.22/1.47  Horn                                    12
% 7.22/1.47  unary                                   8
% 7.22/1.47  binary                                  3
% 7.22/1.47  lits                                    17
% 7.22/1.47  lits eq                                 6
% 7.22/1.47  fd_pure                                 0
% 7.22/1.47  fd_pseudo                               0
% 7.22/1.47  fd_cond                                 1
% 7.22/1.47  fd_pseudo_cond                          0
% 7.22/1.47  AC symbols                              0
% 7.22/1.47  
% 7.22/1.47  ------ Input Options Time Limit: Unbounded
% 7.22/1.47  
% 7.22/1.47  
% 7.22/1.47  ------ 
% 7.22/1.47  Current options:
% 7.22/1.47  ------ 
% 7.22/1.47  
% 7.22/1.47  
% 7.22/1.47  
% 7.22/1.47  
% 7.22/1.47  ------ Proving...
% 7.22/1.47  
% 7.22/1.47  
% 7.22/1.47  % SZS status Theorem for theBenchmark.p
% 7.22/1.47  
% 7.22/1.47  % SZS output start CNFRefutation for theBenchmark.p
% 7.22/1.47  
% 7.22/1.47  fof(f2,axiom,(
% 7.22/1.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f26,plain,(
% 7.22/1.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.22/1.47    inference(cnf_transformation,[],[f2])).
% 7.22/1.47  
% 7.22/1.47  fof(f13,conjecture,(
% 7.22/1.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f14,negated_conjecture,(
% 7.22/1.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.22/1.47    inference(negated_conjecture,[],[f13])).
% 7.22/1.47  
% 7.22/1.47  fof(f15,plain,(
% 7.22/1.47    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 7.22/1.47    inference(pure_predicate_removal,[],[f14])).
% 7.22/1.47  
% 7.22/1.47  fof(f21,plain,(
% 7.22/1.47    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0))),
% 7.22/1.47    inference(ennf_transformation,[],[f15])).
% 7.22/1.47  
% 7.22/1.47  fof(f23,plain,(
% 7.22/1.47    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 7.22/1.47    introduced(choice_axiom,[])).
% 7.22/1.47  
% 7.22/1.47  fof(f22,plain,(
% 7.22/1.47    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_relat_1(sK0))),
% 7.22/1.47    introduced(choice_axiom,[])).
% 7.22/1.47  
% 7.22/1.47  fof(f24,plain,(
% 7.22/1.47    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_relat_1(sK0)),
% 7.22/1.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 7.22/1.47  
% 7.22/1.47  fof(f39,plain,(
% 7.22/1.47    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 7.22/1.47    inference(cnf_transformation,[],[f24])).
% 7.22/1.47  
% 7.22/1.47  fof(f1,axiom,(
% 7.22/1.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f16,plain,(
% 7.22/1.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.22/1.47    inference(ennf_transformation,[],[f1])).
% 7.22/1.47  
% 7.22/1.47  fof(f17,plain,(
% 7.22/1.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.22/1.47    inference(flattening,[],[f16])).
% 7.22/1.47  
% 7.22/1.47  fof(f25,plain,(
% 7.22/1.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.22/1.47    inference(cnf_transformation,[],[f17])).
% 7.22/1.47  
% 7.22/1.47  fof(f6,axiom,(
% 7.22/1.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f19,plain,(
% 7.22/1.47    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.22/1.47    inference(ennf_transformation,[],[f6])).
% 7.22/1.47  
% 7.22/1.47  fof(f31,plain,(
% 7.22/1.47    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.22/1.47    inference(cnf_transformation,[],[f19])).
% 7.22/1.47  
% 7.22/1.47  fof(f5,axiom,(
% 7.22/1.47    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f18,plain,(
% 7.22/1.47    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 7.22/1.47    inference(ennf_transformation,[],[f5])).
% 7.22/1.47  
% 7.22/1.47  fof(f30,plain,(
% 7.22/1.47    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 7.22/1.47    inference(cnf_transformation,[],[f18])).
% 7.22/1.47  
% 7.22/1.47  fof(f38,plain,(
% 7.22/1.47    v1_relat_1(sK0)),
% 7.22/1.47    inference(cnf_transformation,[],[f24])).
% 7.22/1.47  
% 7.22/1.47  fof(f12,axiom,(
% 7.22/1.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f20,plain,(
% 7.22/1.47    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.22/1.47    inference(ennf_transformation,[],[f12])).
% 7.22/1.47  
% 7.22/1.47  fof(f37,plain,(
% 7.22/1.47    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.22/1.47    inference(cnf_transformation,[],[f20])).
% 7.22/1.47  
% 7.22/1.47  fof(f4,axiom,(
% 7.22/1.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f28,plain,(
% 7.22/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.22/1.47    inference(cnf_transformation,[],[f4])).
% 7.22/1.47  
% 7.22/1.47  fof(f45,plain,(
% 7.22/1.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.22/1.47    inference(definition_unfolding,[],[f37,f28])).
% 7.22/1.47  
% 7.22/1.47  fof(f7,axiom,(
% 7.22/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f32,plain,(
% 7.22/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.22/1.47    inference(cnf_transformation,[],[f7])).
% 7.22/1.47  
% 7.22/1.47  fof(f8,axiom,(
% 7.22/1.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f33,plain,(
% 7.22/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.22/1.47    inference(cnf_transformation,[],[f8])).
% 7.22/1.47  
% 7.22/1.47  fof(f9,axiom,(
% 7.22/1.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f34,plain,(
% 7.22/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.22/1.47    inference(cnf_transformation,[],[f9])).
% 7.22/1.47  
% 7.22/1.47  fof(f10,axiom,(
% 7.22/1.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f35,plain,(
% 7.22/1.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.22/1.47    inference(cnf_transformation,[],[f10])).
% 7.22/1.47  
% 7.22/1.47  fof(f41,plain,(
% 7.22/1.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 7.22/1.47    inference(definition_unfolding,[],[f34,f35])).
% 7.22/1.47  
% 7.22/1.47  fof(f42,plain,(
% 7.22/1.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.22/1.47    inference(definition_unfolding,[],[f33,f41])).
% 7.22/1.47  
% 7.22/1.47  fof(f43,plain,(
% 7.22/1.47    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 7.22/1.47    inference(definition_unfolding,[],[f32,f42,f42])).
% 7.22/1.47  
% 7.22/1.47  fof(f11,axiom,(
% 7.22/1.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f36,plain,(
% 7.22/1.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.22/1.47    inference(cnf_transformation,[],[f11])).
% 7.22/1.47  
% 7.22/1.47  fof(f44,plain,(
% 7.22/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 7.22/1.47    inference(definition_unfolding,[],[f36,f28,f42])).
% 7.22/1.47  
% 7.22/1.47  fof(f3,axiom,(
% 7.22/1.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.22/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.22/1.47  
% 7.22/1.47  fof(f27,plain,(
% 7.22/1.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.22/1.47    inference(cnf_transformation,[],[f3])).
% 7.22/1.47  
% 7.22/1.47  fof(f40,plain,(
% 7.22/1.47    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 7.22/1.47    inference(cnf_transformation,[],[f24])).
% 7.22/1.47  
% 7.22/1.47  cnf(c_1,plain,
% 7.22/1.47      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.22/1.47      inference(cnf_transformation,[],[f26]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_255,plain,
% 7.22/1.47      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.22/1.47      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_10,negated_conjecture,
% 7.22/1.47      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 7.22/1.47      inference(cnf_transformation,[],[f39]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_250,plain,
% 7.22/1.47      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 7.22/1.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_0,plain,
% 7.22/1.47      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.22/1.47      inference(cnf_transformation,[],[f25]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_256,plain,
% 7.22/1.47      ( r1_tarski(X0,X1) != iProver_top
% 7.22/1.47      | r1_tarski(X2,X0) != iProver_top
% 7.22/1.47      | r1_tarski(X2,X1) = iProver_top ),
% 7.22/1.47      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_1148,plain,
% 7.22/1.47      ( r1_tarski(X0,k10_relat_1(sK0,sK2)) != iProver_top
% 7.22/1.47      | r1_tarski(X0,sK1) = iProver_top ),
% 7.22/1.47      inference(superposition,[status(thm)],[c_250,c_256]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_1589,plain,
% 7.22/1.47      ( r1_tarski(k4_xboole_0(k10_relat_1(sK0,sK2),X0),sK1) = iProver_top ),
% 7.22/1.47      inference(superposition,[status(thm)],[c_255,c_1148]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_5,plain,
% 7.22/1.47      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 7.22/1.47      inference(cnf_transformation,[],[f31]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_252,plain,
% 7.22/1.47      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 7.22/1.47      | r1_tarski(X0,X2) != iProver_top ),
% 7.22/1.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_3,plain,
% 7.22/1.47      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 7.22/1.47      inference(cnf_transformation,[],[f30]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_254,plain,
% 7.22/1.47      ( k1_xboole_0 = X0 | r1_xboole_0(X0,X0) != iProver_top ),
% 7.22/1.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_615,plain,
% 7.22/1.47      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.22/1.47      | r1_tarski(k4_xboole_0(X0,X1),X1) != iProver_top ),
% 7.22/1.47      inference(superposition,[status(thm)],[c_252,c_254]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_2285,plain,
% 7.22/1.47      ( k4_xboole_0(k10_relat_1(sK0,sK2),sK1) = k1_xboole_0 ),
% 7.22/1.47      inference(superposition,[status(thm)],[c_1589,c_615]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_11,negated_conjecture,
% 7.22/1.47      ( v1_relat_1(sK0) ),
% 7.22/1.47      inference(cnf_transformation,[],[f38]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_249,plain,
% 7.22/1.47      ( v1_relat_1(sK0) = iProver_top ),
% 7.22/1.47      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_8,plain,
% 7.22/1.47      ( ~ v1_relat_1(X0)
% 7.22/1.47      | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.22/1.47      inference(cnf_transformation,[],[f45]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_251,plain,
% 7.22/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 7.22/1.47      | v1_relat_1(X1) != iProver_top ),
% 7.22/1.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_2698,plain,
% 7.22/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 7.22/1.47      inference(superposition,[status(thm)],[c_249,c_251]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_6,plain,
% 7.22/1.47      ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
% 7.22/1.47      inference(cnf_transformation,[],[f43]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_7,plain,
% 7.22/1.47      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.22/1.47      inference(cnf_transformation,[],[f44]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_688,plain,
% 7.22/1.47      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.22/1.47      inference(superposition,[status(thm)],[c_6,c_7]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_734,plain,
% 7.22/1.47      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.22/1.47      inference(superposition,[status(thm)],[c_688,c_7]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_2911,plain,
% 7.22/1.47      ( k4_xboole_0(k10_relat_1(sK0,X0),k4_xboole_0(k10_relat_1(sK0,X0),X1)) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 7.22/1.47      inference(superposition,[status(thm)],[c_2698,c_734]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_32063,plain,
% 7.22/1.47      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k4_xboole_0(k10_relat_1(sK0,sK2),k1_xboole_0) ),
% 7.22/1.47      inference(superposition,[status(thm)],[c_2285,c_2911]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_2,plain,
% 7.22/1.47      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.22/1.47      inference(cnf_transformation,[],[f27]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_32068,plain,
% 7.22/1.47      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 7.22/1.47      inference(demodulation,[status(thm)],[c_32063,c_2]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_9,negated_conjecture,
% 7.22/1.47      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 7.22/1.47      inference(cnf_transformation,[],[f40]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_32386,plain,
% 7.22/1.47      ( k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 7.22/1.47      inference(demodulation,[status(thm)],[c_32068,c_9]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_85,plain,( X0 = X0 ),theory(equality) ).
% 7.22/1.47  
% 7.22/1.47  cnf(c_563,plain,
% 7.22/1.47      ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 7.22/1.47      inference(instantiation,[status(thm)],[c_85]) ).
% 7.22/1.47  
% 7.22/1.47  cnf(contradiction,plain,
% 7.22/1.47      ( $false ),
% 7.22/1.47      inference(minisat,[status(thm)],[c_32386,c_563]) ).
% 7.22/1.47  
% 7.22/1.47  
% 7.22/1.47  % SZS output end CNFRefutation for theBenchmark.p
% 7.22/1.47  
% 7.22/1.47  ------                               Statistics
% 7.22/1.47  
% 7.22/1.47  ------ Selected
% 7.22/1.47  
% 7.22/1.47  total_time:                             0.995
% 7.22/1.47  
%------------------------------------------------------------------------------
