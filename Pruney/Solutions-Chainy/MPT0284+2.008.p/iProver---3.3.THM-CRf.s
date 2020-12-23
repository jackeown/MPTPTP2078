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
% DateTime   : Thu Dec  3 11:36:39 EST 2020

% Result     : Theorem 11.49s
% Output     : CNFRefutation 11.49s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 126 expanded)
%              Number of clauses        :   21 (  30 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 422 expanded)
%              Number of equality atoms :   27 (  62 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f45,f45])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f12,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3))) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f28])).

fof(f46,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f55,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
    inference(definition_unfolding,[],[f46,f45,f47])).

cnf(c_182,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_184,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2580,plain,
    ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
    | r1_tarski(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_182,c_184])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8739,plain,
    ( ~ r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
    | r1_tarski(X3,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1))))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_2580,c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_658,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1521,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_tarski(sK0(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))),X2) ),
    inference(resolution,[status(thm)],[c_658,c_5])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_643,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0),X1),X0)
    | r1_tarski(k1_zfmisc_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_13,c_3])).

cnf(c_24809,plain,
    ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k3_tarski(k2_tarski(X1,X0)))) ),
    inference(resolution,[status(thm)],[c_1521,c_643])).

cnf(c_45538,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
    | X0 != k1_zfmisc_1(X1) ),
    inference(resolution,[status(thm)],[c_8739,c_24809])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1306,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK3,sK2)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2)))))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
    inference(resolution,[status(thm)],[c_9,c_14])).

cnf(c_24828,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_24809,c_1306])).

cnf(c_46283,plain,
    ( k1_zfmisc_1(k4_xboole_0(sK2,sK3)) != k1_zfmisc_1(k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_45538,c_24828])).

cnf(c_46284,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_46283])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:33:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 11.49/2.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.49/2.02  
% 11.49/2.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.49/2.02  
% 11.49/2.02  ------  iProver source info
% 11.49/2.02  
% 11.49/2.02  git: date: 2020-06-30 10:37:57 +0100
% 11.49/2.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.49/2.02  git: non_committed_changes: false
% 11.49/2.02  git: last_make_outside_of_git: false
% 11.49/2.02  
% 11.49/2.02  ------ 
% 11.49/2.02  ------ Parsing...
% 11.49/2.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.49/2.02  
% 11.49/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.49/2.02  
% 11.49/2.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.49/2.02  
% 11.49/2.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.49/2.02  ------ Proving...
% 11.49/2.02  ------ Problem Properties 
% 11.49/2.02  
% 11.49/2.02  
% 11.49/2.02  clauses                                 15
% 11.49/2.02  conjectures                             1
% 11.49/2.02  EPR                                     1
% 11.49/2.02  Horn                                    13
% 11.49/2.02  unary                                   5
% 11.49/2.02  binary                                  6
% 11.49/2.02  lits                                    29
% 11.49/2.02  lits eq                                 6
% 11.49/2.02  fd_pure                                 0
% 11.49/2.02  fd_pseudo                               0
% 11.49/2.02  fd_cond                                 0
% 11.49/2.02  fd_pseudo_cond                          2
% 11.49/2.02  AC symbols                              0
% 11.49/2.02  
% 11.49/2.02  ------ Input Options Time Limit: Unbounded
% 11.49/2.02  
% 11.49/2.02  
% 11.49/2.02  ------ 
% 11.49/2.02  Current options:
% 11.49/2.02  ------ 
% 11.49/2.02  
% 11.49/2.02  
% 11.49/2.02  
% 11.49/2.02  
% 11.49/2.02  ------ Proving...
% 11.49/2.02  
% 11.49/2.02  
% 11.49/2.02  % SZS status Theorem for theBenchmark.p
% 11.49/2.02  
% 11.49/2.02   Resolution empty clause
% 11.49/2.02  
% 11.49/2.02  % SZS output start CNFRefutation for theBenchmark.p
% 11.49/2.02  
% 11.49/2.02  fof(f1,axiom,(
% 11.49/2.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.49/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f30,plain,(
% 11.49/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.49/2.02    inference(cnf_transformation,[],[f1])).
% 11.49/2.02  
% 11.49/2.02  fof(f11,axiom,(
% 11.49/2.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.49/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f45,plain,(
% 11.49/2.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.49/2.02    inference(cnf_transformation,[],[f11])).
% 11.49/2.02  
% 11.49/2.02  fof(f49,plain,(
% 11.49/2.02    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 11.49/2.02    inference(definition_unfolding,[],[f30,f45,f45])).
% 11.49/2.02  
% 11.49/2.02  fof(f2,axiom,(
% 11.49/2.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.49/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f14,plain,(
% 11.49/2.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.49/2.02    inference(ennf_transformation,[],[f2])).
% 11.49/2.02  
% 11.49/2.02  fof(f20,plain,(
% 11.49/2.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.49/2.02    inference(nnf_transformation,[],[f14])).
% 11.49/2.02  
% 11.49/2.02  fof(f21,plain,(
% 11.49/2.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.49/2.02    inference(rectify,[],[f20])).
% 11.49/2.02  
% 11.49/2.02  fof(f22,plain,(
% 11.49/2.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 11.49/2.02    introduced(choice_axiom,[])).
% 11.49/2.02  
% 11.49/2.02  fof(f23,plain,(
% 11.49/2.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.49/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 11.49/2.02  
% 11.49/2.02  fof(f33,plain,(
% 11.49/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 11.49/2.02    inference(cnf_transformation,[],[f23])).
% 11.49/2.02  
% 11.49/2.02  fof(f10,axiom,(
% 11.49/2.02    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.49/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f24,plain,(
% 11.49/2.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.49/2.02    inference(nnf_transformation,[],[f10])).
% 11.49/2.02  
% 11.49/2.02  fof(f25,plain,(
% 11.49/2.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.49/2.02    inference(rectify,[],[f24])).
% 11.49/2.02  
% 11.49/2.02  fof(f26,plain,(
% 11.49/2.02    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 11.49/2.02    introduced(choice_axiom,[])).
% 11.49/2.02  
% 11.49/2.02  fof(f27,plain,(
% 11.49/2.02    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.49/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 11.49/2.02  
% 11.49/2.02  fof(f42,plain,(
% 11.49/2.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 11.49/2.02    inference(cnf_transformation,[],[f27])).
% 11.49/2.02  
% 11.49/2.02  fof(f56,plain,(
% 11.49/2.02    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 11.49/2.02    inference(equality_resolution,[],[f42])).
% 11.49/2.02  
% 11.49/2.02  fof(f5,axiom,(
% 11.49/2.02    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 11.49/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f15,plain,(
% 11.49/2.02    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.49/2.02    inference(ennf_transformation,[],[f5])).
% 11.49/2.02  
% 11.49/2.02  fof(f36,plain,(
% 11.49/2.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.49/2.02    inference(cnf_transformation,[],[f15])).
% 11.49/2.02  
% 11.49/2.02  fof(f50,plain,(
% 11.49/2.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 11.49/2.02    inference(definition_unfolding,[],[f36,f45])).
% 11.49/2.02  
% 11.49/2.02  fof(f41,plain,(
% 11.49/2.02    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.49/2.02    inference(cnf_transformation,[],[f27])).
% 11.49/2.02  
% 11.49/2.02  fof(f57,plain,(
% 11.49/2.02    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.49/2.02    inference(equality_resolution,[],[f41])).
% 11.49/2.02  
% 11.49/2.02  fof(f32,plain,(
% 11.49/2.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 11.49/2.02    inference(cnf_transformation,[],[f23])).
% 11.49/2.02  
% 11.49/2.02  fof(f9,axiom,(
% 11.49/2.02    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 11.49/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f17,plain,(
% 11.49/2.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 11.49/2.02    inference(ennf_transformation,[],[f9])).
% 11.49/2.02  
% 11.49/2.02  fof(f18,plain,(
% 11.49/2.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 11.49/2.02    inference(flattening,[],[f17])).
% 11.49/2.02  
% 11.49/2.02  fof(f40,plain,(
% 11.49/2.02    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.49/2.02    inference(cnf_transformation,[],[f18])).
% 11.49/2.02  
% 11.49/2.02  fof(f54,plain,(
% 11.49/2.02    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.49/2.02    inference(definition_unfolding,[],[f40,f45])).
% 11.49/2.02  
% 11.49/2.02  fof(f12,conjecture,(
% 11.49/2.02    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 11.49/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f13,negated_conjecture,(
% 11.49/2.02    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 11.49/2.02    inference(negated_conjecture,[],[f12])).
% 11.49/2.02  
% 11.49/2.02  fof(f19,plain,(
% 11.49/2.02    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 11.49/2.02    inference(ennf_transformation,[],[f13])).
% 11.49/2.02  
% 11.49/2.02  fof(f28,plain,(
% 11.49/2.02    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3)))),
% 11.49/2.02    introduced(choice_axiom,[])).
% 11.49/2.02  
% 11.49/2.02  fof(f29,plain,(
% 11.49/2.02    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3)))),
% 11.49/2.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f28])).
% 11.49/2.02  
% 11.49/2.02  fof(f46,plain,(
% 11.49/2.02    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3)))),
% 11.49/2.02    inference(cnf_transformation,[],[f29])).
% 11.49/2.02  
% 11.49/2.02  fof(f3,axiom,(
% 11.49/2.02    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 11.49/2.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.49/2.02  
% 11.49/2.02  fof(f34,plain,(
% 11.49/2.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 11.49/2.02    inference(cnf_transformation,[],[f3])).
% 11.49/2.02  
% 11.49/2.02  fof(f47,plain,(
% 11.49/2.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 11.49/2.02    inference(definition_unfolding,[],[f34,f45])).
% 11.49/2.02  
% 11.49/2.02  fof(f55,plain,(
% 11.49/2.02    ~r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2)))))),
% 11.49/2.02    inference(definition_unfolding,[],[f46,f45,f47])).
% 11.49/2.02  
% 11.49/2.02  cnf(c_182,plain,
% 11.49/2.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.49/2.02      theory(equality) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_184,plain,
% 11.49/2.02      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.49/2.02      theory(equality) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_2580,plain,
% 11.49/2.02      ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
% 11.49/2.02      | r1_tarski(X2,k1_zfmisc_1(X3))
% 11.49/2.02      | X2 != X0
% 11.49/2.02      | X3 != X1 ),
% 11.49/2.02      inference(resolution,[status(thm)],[c_182,c_184]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_1,plain,
% 11.49/2.02      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 11.49/2.02      inference(cnf_transformation,[],[f49]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_8739,plain,
% 11.49/2.02      ( ~ r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
% 11.49/2.02      | r1_tarski(X3,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1))))
% 11.49/2.02      | X3 != X0 ),
% 11.49/2.02      inference(resolution,[status(thm)],[c_2580,c_1]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_2,plain,
% 11.49/2.02      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 11.49/2.02      inference(cnf_transformation,[],[f33]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_12,plain,
% 11.49/2.02      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.49/2.02      inference(cnf_transformation,[],[f56]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_658,plain,
% 11.49/2.02      ( r1_tarski(X0,k1_zfmisc_1(X1))
% 11.49/2.02      | ~ r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) ),
% 11.49/2.02      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_5,plain,
% 11.49/2.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 11.49/2.02      inference(cnf_transformation,[],[f50]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_1521,plain,
% 11.49/2.02      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
% 11.49/2.02      | ~ r1_tarski(sK0(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))),X2) ),
% 11.49/2.02      inference(resolution,[status(thm)],[c_658,c_5]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_13,plain,
% 11.49/2.02      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.49/2.02      inference(cnf_transformation,[],[f57]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_3,plain,
% 11.49/2.02      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 11.49/2.02      inference(cnf_transformation,[],[f32]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_643,plain,
% 11.49/2.02      ( r1_tarski(sK0(k1_zfmisc_1(X0),X1),X0) | r1_tarski(k1_zfmisc_1(X0),X1) ),
% 11.49/2.02      inference(resolution,[status(thm)],[c_13,c_3]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_24809,plain,
% 11.49/2.02      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k3_tarski(k2_tarski(X1,X0)))) ),
% 11.49/2.02      inference(resolution,[status(thm)],[c_1521,c_643]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_45538,plain,
% 11.49/2.02      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
% 11.49/2.02      | X0 != k1_zfmisc_1(X1) ),
% 11.49/2.02      inference(resolution,[status(thm)],[c_8739,c_24809]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_9,plain,
% 11.49/2.02      ( ~ r1_tarski(X0,X1)
% 11.49/2.02      | ~ r1_tarski(X2,X1)
% 11.49/2.02      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 11.49/2.02      inference(cnf_transformation,[],[f54]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_14,negated_conjecture,
% 11.49/2.02      ( ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
% 11.49/2.02      inference(cnf_transformation,[],[f55]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_1306,plain,
% 11.49/2.02      ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK3,sK2)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2)))))
% 11.49/2.02      | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
% 11.49/2.02      inference(resolution,[status(thm)],[c_9,c_14]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_24828,plain,
% 11.49/2.02      ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
% 11.49/2.02      inference(backward_subsumption_resolution,[status(thm)],[c_24809,c_1306]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_46283,plain,
% 11.49/2.02      ( k1_zfmisc_1(k4_xboole_0(sK2,sK3)) != k1_zfmisc_1(k4_xboole_0(sK2,sK3)) ),
% 11.49/2.02      inference(resolution,[status(thm)],[c_45538,c_24828]) ).
% 11.49/2.02  
% 11.49/2.02  cnf(c_46284,plain,
% 11.49/2.02      ( $false ),
% 11.49/2.02      inference(equality_resolution_simp,[status(thm)],[c_46283]) ).
% 11.49/2.02  
% 11.49/2.02  
% 11.49/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.49/2.02  
% 11.49/2.02  ------                               Statistics
% 11.49/2.02  
% 11.49/2.02  ------ Selected
% 11.49/2.02  
% 11.49/2.02  total_time:                             1.455
% 11.49/2.02  
%------------------------------------------------------------------------------
