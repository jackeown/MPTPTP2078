%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:48 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   51 (  95 expanded)
%              Number of clauses        :   29 (  36 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :   88 ( 225 expanded)
%              Number of equality atoms :   64 ( 140 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,
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

fof(f13,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).

fof(f20,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f21,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_7,negated_conjecture,
    ( r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_51,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_7])).

cnf(c_52,plain,
    ( k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_51])).

cnf(c_4,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_396,plain,
    ( k3_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k2_xboole_0(k3_xboole_0(sK2,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_52,c_4])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_8,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_80,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_8])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_270,plain,
    ( k3_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = sK2 ),
    inference(superposition,[status(thm)],[c_80,c_3])).

cnf(c_842,plain,
    ( k2_xboole_0(k3_xboole_0(sK2,sK1),k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_396,c_270])).

cnf(c_2034,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_1,c_842])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_46,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_6])).

cnf(c_47,plain,
    ( k3_xboole_0(sK3,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_46])).

cnf(c_174,plain,
    ( k3_xboole_0(sK1,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_47,c_1])).

cnf(c_397,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(X0,sK3)) = k2_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_174,c_4])).

cnf(c_1657,plain,
    ( k3_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k2_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_80,c_397])).

cnf(c_1677,plain,
    ( k2_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_1657,c_3])).

cnf(c_2799,plain,
    ( sK2 = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2034,c_1677])).

cnf(c_63,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_92,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_93,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_62,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_66,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_5,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2799,c_93,c_66,c_5])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.49/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/1.00  
% 3.49/1.00  ------  iProver source info
% 3.49/1.00  
% 3.49/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.49/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/1.00  git: non_committed_changes: false
% 3.49/1.00  git: last_make_outside_of_git: false
% 3.49/1.00  
% 3.49/1.00  ------ 
% 3.49/1.00  ------ Parsing...
% 3.49/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/1.00  
% 3.49/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.49/1.00  ------ Proving...
% 3.49/1.00  ------ Problem Properties 
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  clauses                                 8
% 3.49/1.00  conjectures                             2
% 3.49/1.00  EPR                                     1
% 3.49/1.00  Horn                                    8
% 3.49/1.00  unary                                   8
% 3.49/1.00  binary                                  0
% 3.49/1.00  lits                                    8
% 3.49/1.00  lits eq                                 8
% 3.49/1.00  fd_pure                                 0
% 3.49/1.00  fd_pseudo                               0
% 3.49/1.00  fd_cond                                 0
% 3.49/1.00  fd_pseudo_cond                          0
% 3.49/1.00  AC symbols                              0
% 3.49/1.00  
% 3.49/1.00  ------ Input Options Time Limit: Unbounded
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  ------ 
% 3.49/1.00  Current options:
% 3.49/1.00  ------ 
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  ------ Proving...
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  % SZS status Theorem for theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  fof(f2,axiom,(
% 3.49/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f15,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f2])).
% 3.49/1.00  
% 3.49/1.00  fof(f3,axiom,(
% 3.49/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f8,plain,(
% 3.49/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.49/1.00    inference(unused_predicate_definition_removal,[],[f3])).
% 3.49/1.00  
% 3.49/1.00  fof(f9,plain,(
% 3.49/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 3.49/1.00    inference(ennf_transformation,[],[f8])).
% 3.49/1.00  
% 3.49/1.00  fof(f16,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f9])).
% 3.49/1.00  
% 3.49/1.00  fof(f6,conjecture,(
% 3.49/1.00    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f7,negated_conjecture,(
% 3.49/1.00    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 3.49/1.00    inference(negated_conjecture,[],[f6])).
% 3.49/1.00  
% 3.49/1.00  fof(f10,plain,(
% 3.49/1.00    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 3.49/1.00    inference(ennf_transformation,[],[f7])).
% 3.49/1.00  
% 3.49/1.00  fof(f11,plain,(
% 3.49/1.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 3.49/1.00    inference(flattening,[],[f10])).
% 3.49/1.00  
% 3.49/1.00  fof(f12,plain,(
% 3.49/1.00    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 3.49/1.00    introduced(choice_axiom,[])).
% 3.49/1.00  
% 3.49/1.00  fof(f13,plain,(
% 3.49/1.00    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.49/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).
% 3.49/1.00  
% 3.49/1.00  fof(f20,plain,(
% 3.49/1.00    r1_xboole_0(sK2,sK0)),
% 3.49/1.00    inference(cnf_transformation,[],[f13])).
% 3.49/1.00  
% 3.49/1.00  fof(f5,axiom,(
% 3.49/1.00    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f18,plain,(
% 3.49/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.49/1.00    inference(cnf_transformation,[],[f5])).
% 3.49/1.00  
% 3.49/1.00  fof(f1,axiom,(
% 3.49/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f14,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.49/1.00    inference(cnf_transformation,[],[f1])).
% 3.49/1.00  
% 3.49/1.00  fof(f19,plain,(
% 3.49/1.00    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 3.49/1.00    inference(cnf_transformation,[],[f13])).
% 3.49/1.00  
% 3.49/1.00  fof(f4,axiom,(
% 3.49/1.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.49/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/1.00  
% 3.49/1.00  fof(f17,plain,(
% 3.49/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.49/1.00    inference(cnf_transformation,[],[f4])).
% 3.49/1.00  
% 3.49/1.00  fof(f21,plain,(
% 3.49/1.00    r1_xboole_0(sK3,sK1)),
% 3.49/1.00    inference(cnf_transformation,[],[f13])).
% 3.49/1.00  
% 3.49/1.00  fof(f22,plain,(
% 3.49/1.00    sK1 != sK2),
% 3.49/1.00    inference(cnf_transformation,[],[f13])).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1,plain,
% 3.49/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f15]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2,plain,
% 3.49/1.00      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.49/1.00      inference(cnf_transformation,[],[f16]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_7,negated_conjecture,
% 3.49/1.00      ( r1_xboole_0(sK2,sK0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f20]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_51,plain,
% 3.49/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK0 != X1 | sK2 != X0 ),
% 3.49/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_7]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_52,plain,
% 3.49/1.00      ( k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
% 3.49/1.00      inference(unflattening,[status(thm)],[c_51]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_4,plain,
% 3.49/1.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.49/1.00      inference(cnf_transformation,[],[f18]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_396,plain,
% 3.49/1.00      ( k3_xboole_0(sK2,k2_xboole_0(X0,sK0)) = k2_xboole_0(k3_xboole_0(sK2,X0),k1_xboole_0) ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_52,c_4]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_0,plain,
% 3.49/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.49/1.00      inference(cnf_transformation,[],[f14]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_8,negated_conjecture,
% 3.49/1.00      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
% 3.49/1.00      inference(cnf_transformation,[],[f19]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_80,plain,
% 3.49/1.00      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK3) ),
% 3.49/1.00      inference(demodulation,[status(thm)],[c_0,c_8]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_3,plain,
% 3.49/1.00      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 3.49/1.00      inference(cnf_transformation,[],[f17]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_270,plain,
% 3.49/1.00      ( k3_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = sK2 ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_80,c_3]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_842,plain,
% 3.49/1.00      ( k2_xboole_0(k3_xboole_0(sK2,sK1),k1_xboole_0) = sK2 ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_396,c_270]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2034,plain,
% 3.49/1.00      ( k2_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0) = sK2 ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_1,c_842]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_6,negated_conjecture,
% 3.49/1.00      ( r1_xboole_0(sK3,sK1) ),
% 3.49/1.00      inference(cnf_transformation,[],[f21]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_46,plain,
% 3.49/1.00      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X0 | sK1 != X1 ),
% 3.49/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_6]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_47,plain,
% 3.49/1.00      ( k3_xboole_0(sK3,sK1) = k1_xboole_0 ),
% 3.49/1.00      inference(unflattening,[status(thm)],[c_46]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_174,plain,
% 3.49/1.00      ( k3_xboole_0(sK1,sK3) = k1_xboole_0 ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_47,c_1]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_397,plain,
% 3.49/1.00      ( k3_xboole_0(sK1,k2_xboole_0(X0,sK3)) = k2_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0) ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_174,c_4]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1657,plain,
% 3.49/1.00      ( k3_xboole_0(sK1,k2_xboole_0(sK1,sK0)) = k2_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0) ),
% 3.49/1.00      inference(superposition,[status(thm)],[c_80,c_397]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_1677,plain,
% 3.49/1.00      ( k2_xboole_0(k3_xboole_0(sK1,sK2),k1_xboole_0) = sK1 ),
% 3.49/1.00      inference(demodulation,[status(thm)],[c_1657,c_3]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_2799,plain,
% 3.49/1.00      ( sK2 = sK1 ),
% 3.49/1.00      inference(light_normalisation,[status(thm)],[c_2034,c_1677]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_63,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_92,plain,
% 3.49/1.00      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_63]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_93,plain,
% 3.49/1.00      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_92]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_62,plain,( X0 = X0 ),theory(equality) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_66,plain,
% 3.49/1.00      ( sK1 = sK1 ),
% 3.49/1.00      inference(instantiation,[status(thm)],[c_62]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(c_5,negated_conjecture,
% 3.49/1.00      ( sK1 != sK2 ),
% 3.49/1.00      inference(cnf_transformation,[],[f22]) ).
% 3.49/1.00  
% 3.49/1.00  cnf(contradiction,plain,
% 3.49/1.00      ( $false ),
% 3.49/1.00      inference(minisat,[status(thm)],[c_2799,c_93,c_66,c_5]) ).
% 3.49/1.00  
% 3.49/1.00  
% 3.49/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/1.00  
% 3.49/1.00  ------                               Statistics
% 3.49/1.00  
% 3.49/1.00  ------ Selected
% 3.49/1.00  
% 3.49/1.00  total_time:                             0.169
% 3.49/1.00  
%------------------------------------------------------------------------------
