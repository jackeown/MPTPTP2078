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
% DateTime   : Thu Dec  3 11:47:48 EST 2020

% Result     : Theorem 11.78s
% Output     : CNFRefutation 11.78s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of clauses        :   26 (  31 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 146 expanded)
%              Number of equality atoms :   41 (  54 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f25,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_61,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_114,plain,
    ( X0 != X1
    | k4_xboole_0(X1,X2) = k1_xboole_0
    | k2_xboole_0(X0,X3) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_61,c_5])).

cnf(c_115,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_114])).

cnf(c_783,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_115])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_794,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_783,c_4])).

cnf(c_916,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_794,c_1])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_125,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_61,c_8])).

cnf(c_126,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_125])).

cnf(c_387,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_126,c_4])).

cnf(c_388,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_0,c_387])).

cnf(c_1082,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_916,c_388])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_9,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_106,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_107,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_106])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_130,plain,
    ( k10_relat_1(sK2,sK0) != X0
    | k2_xboole_0(X0,X1) != k10_relat_1(sK2,sK1) ),
    inference(resolution_lifted,[status(thm)],[c_5,c_7])).

cnf(c_131,plain,
    ( k2_xboole_0(k10_relat_1(sK2,sK0),X0) != k10_relat_1(sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_130])).

cnf(c_498,plain,
    ( k10_relat_1(sK2,k2_xboole_0(sK0,X0)) != k10_relat_1(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_107,c_131])).

cnf(c_45624,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1082,c_498])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.78/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.78/2.00  
% 11.78/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.78/2.00  
% 11.78/2.00  ------  iProver source info
% 11.78/2.00  
% 11.78/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.78/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.78/2.00  git: non_committed_changes: false
% 11.78/2.00  git: last_make_outside_of_git: false
% 11.78/2.00  
% 11.78/2.00  ------ 
% 11.78/2.00  ------ Parsing...
% 11.78/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.78/2.00  
% 11.78/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.78/2.00  
% 11.78/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.78/2.00  
% 11.78/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.78/2.00  ------ Proving...
% 11.78/2.00  ------ Problem Properties 
% 11.78/2.00  
% 11.78/2.00  
% 11.78/2.00  clauses                                 9
% 11.78/2.00  conjectures                             0
% 11.78/2.00  EPR                                     0
% 11.78/2.00  Horn                                    9
% 11.78/2.00  unary                                   8
% 11.78/2.00  binary                                  1
% 11.78/2.00  lits                                    10
% 11.78/2.00  lits eq                                 10
% 11.78/2.00  fd_pure                                 0
% 11.78/2.00  fd_pseudo                               0
% 11.78/2.00  fd_cond                                 0
% 11.78/2.00  fd_pseudo_cond                          0
% 11.78/2.00  AC symbols                              0
% 11.78/2.00  
% 11.78/2.00  ------ Input Options Time Limit: Unbounded
% 11.78/2.00  
% 11.78/2.00  
% 11.78/2.00  ------ 
% 11.78/2.00  Current options:
% 11.78/2.00  ------ 
% 11.78/2.00  
% 11.78/2.00  
% 11.78/2.00  
% 11.78/2.00  
% 11.78/2.00  ------ Proving...
% 11.78/2.00  
% 11.78/2.00  
% 11.78/2.00  % SZS status Theorem for theBenchmark.p
% 11.78/2.00  
% 11.78/2.00   Resolution empty clause
% 11.78/2.00  
% 11.78/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.78/2.00  
% 11.78/2.00  fof(f2,axiom,(
% 11.78/2.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 11.78/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.00  
% 11.78/2.00  fof(f9,plain,(
% 11.78/2.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 11.78/2.00    inference(rectify,[],[f2])).
% 11.78/2.00  
% 11.78/2.00  fof(f17,plain,(
% 11.78/2.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 11.78/2.00    inference(cnf_transformation,[],[f9])).
% 11.78/2.00  
% 11.78/2.00  fof(f3,axiom,(
% 11.78/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.78/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.00  
% 11.78/2.00  fof(f13,plain,(
% 11.78/2.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.78/2.00    inference(nnf_transformation,[],[f3])).
% 11.78/2.00  
% 11.78/2.00  fof(f19,plain,(
% 11.78/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.78/2.00    inference(cnf_transformation,[],[f13])).
% 11.78/2.00  
% 11.78/2.00  fof(f5,axiom,(
% 11.78/2.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.78/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.00  
% 11.78/2.00  fof(f21,plain,(
% 11.78/2.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.78/2.00    inference(cnf_transformation,[],[f5])).
% 11.78/2.00  
% 11.78/2.00  fof(f4,axiom,(
% 11.78/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.78/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.00  
% 11.78/2.00  fof(f20,plain,(
% 11.78/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.78/2.00    inference(cnf_transformation,[],[f4])).
% 11.78/2.00  
% 11.78/2.00  fof(f1,axiom,(
% 11.78/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.78/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.00  
% 11.78/2.00  fof(f16,plain,(
% 11.78/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.78/2.00    inference(cnf_transformation,[],[f1])).
% 11.78/2.00  
% 11.78/2.00  fof(f7,conjecture,(
% 11.78/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 11.78/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.00  
% 11.78/2.00  fof(f8,negated_conjecture,(
% 11.78/2.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 11.78/2.00    inference(negated_conjecture,[],[f7])).
% 11.78/2.00  
% 11.78/2.00  fof(f11,plain,(
% 11.78/2.00    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 11.78/2.00    inference(ennf_transformation,[],[f8])).
% 11.78/2.00  
% 11.78/2.00  fof(f12,plain,(
% 11.78/2.00    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 11.78/2.00    inference(flattening,[],[f11])).
% 11.78/2.00  
% 11.78/2.00  fof(f14,plain,(
% 11.78/2.00    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 11.78/2.00    introduced(choice_axiom,[])).
% 11.78/2.00  
% 11.78/2.00  fof(f15,plain,(
% 11.78/2.00    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 11.78/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 11.78/2.00  
% 11.78/2.00  fof(f24,plain,(
% 11.78/2.00    r1_tarski(sK0,sK1)),
% 11.78/2.00    inference(cnf_transformation,[],[f15])).
% 11.78/2.00  
% 11.78/2.00  fof(f6,axiom,(
% 11.78/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 11.78/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.78/2.00  
% 11.78/2.00  fof(f10,plain,(
% 11.78/2.00    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 11.78/2.00    inference(ennf_transformation,[],[f6])).
% 11.78/2.00  
% 11.78/2.00  fof(f22,plain,(
% 11.78/2.00    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 11.78/2.00    inference(cnf_transformation,[],[f10])).
% 11.78/2.00  
% 11.78/2.00  fof(f23,plain,(
% 11.78/2.00    v1_relat_1(sK2)),
% 11.78/2.00    inference(cnf_transformation,[],[f15])).
% 11.78/2.00  
% 11.78/2.00  fof(f25,plain,(
% 11.78/2.00    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 11.78/2.00    inference(cnf_transformation,[],[f15])).
% 11.78/2.00  
% 11.78/2.00  cnf(c_1,plain,
% 11.78/2.00      ( k2_xboole_0(X0,X0) = X0 ),
% 11.78/2.00      inference(cnf_transformation,[],[f17]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_2,plain,
% 11.78/2.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.78/2.00      inference(cnf_transformation,[],[f19]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_61,plain,
% 11.78/2.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.78/2.00      inference(prop_impl,[status(thm)],[c_2]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_5,plain,
% 11.78/2.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 11.78/2.00      inference(cnf_transformation,[],[f21]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_114,plain,
% 11.78/2.00      ( X0 != X1
% 11.78/2.00      | k4_xboole_0(X1,X2) = k1_xboole_0
% 11.78/2.00      | k2_xboole_0(X0,X3) != X2 ),
% 11.78/2.00      inference(resolution_lifted,[status(thm)],[c_61,c_5]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_115,plain,
% 11.78/2.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.78/2.00      inference(unflattening,[status(thm)],[c_114]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_783,plain,
% 11.78/2.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 11.78/2.00      inference(superposition,[status(thm)],[c_1,c_115]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_4,plain,
% 11.78/2.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.78/2.00      inference(cnf_transformation,[],[f20]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_794,plain,
% 11.78/2.00      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 11.78/2.00      inference(superposition,[status(thm)],[c_783,c_4]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_916,plain,
% 11.78/2.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.78/2.00      inference(superposition,[status(thm)],[c_794,c_1]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_0,plain,
% 11.78/2.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.78/2.00      inference(cnf_transformation,[],[f16]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_8,negated_conjecture,
% 11.78/2.00      ( r1_tarski(sK0,sK1) ),
% 11.78/2.00      inference(cnf_transformation,[],[f24]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_125,plain,
% 11.78/2.00      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 11.78/2.00      inference(resolution_lifted,[status(thm)],[c_61,c_8]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_126,plain,
% 11.78/2.00      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 11.78/2.00      inference(unflattening,[status(thm)],[c_125]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_387,plain,
% 11.78/2.00      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
% 11.78/2.00      inference(superposition,[status(thm)],[c_126,c_4]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_388,plain,
% 11.78/2.00      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k1_xboole_0) ),
% 11.78/2.00      inference(superposition,[status(thm)],[c_0,c_387]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_1082,plain,
% 11.78/2.00      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 11.78/2.00      inference(superposition,[status(thm)],[c_916,c_388]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_6,plain,
% 11.78/2.00      ( ~ v1_relat_1(X0)
% 11.78/2.00      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 11.78/2.00      inference(cnf_transformation,[],[f22]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_9,negated_conjecture,
% 11.78/2.00      ( v1_relat_1(sK2) ),
% 11.78/2.00      inference(cnf_transformation,[],[f23]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_106,plain,
% 11.78/2.00      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 11.78/2.00      | sK2 != X0 ),
% 11.78/2.00      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_107,plain,
% 11.78/2.00      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
% 11.78/2.00      inference(unflattening,[status(thm)],[c_106]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_7,negated_conjecture,
% 11.78/2.00      ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 11.78/2.00      inference(cnf_transformation,[],[f25]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_130,plain,
% 11.78/2.00      ( k10_relat_1(sK2,sK0) != X0
% 11.78/2.00      | k2_xboole_0(X0,X1) != k10_relat_1(sK2,sK1) ),
% 11.78/2.00      inference(resolution_lifted,[status(thm)],[c_5,c_7]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_131,plain,
% 11.78/2.00      ( k2_xboole_0(k10_relat_1(sK2,sK0),X0) != k10_relat_1(sK2,sK1) ),
% 11.78/2.00      inference(unflattening,[status(thm)],[c_130]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_498,plain,
% 11.78/2.00      ( k10_relat_1(sK2,k2_xboole_0(sK0,X0)) != k10_relat_1(sK2,sK1) ),
% 11.78/2.00      inference(superposition,[status(thm)],[c_107,c_131]) ).
% 11.78/2.00  
% 11.78/2.00  cnf(c_45624,plain,
% 11.78/2.00      ( $false ),
% 11.78/2.00      inference(superposition,[status(thm)],[c_1082,c_498]) ).
% 11.78/2.00  
% 11.78/2.00  
% 11.78/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.78/2.00  
% 11.78/2.00  ------                               Statistics
% 11.78/2.00  
% 11.78/2.00  ------ Selected
% 11.78/2.00  
% 11.78/2.00  total_time:                             1.432
% 11.78/2.00  
%------------------------------------------------------------------------------
