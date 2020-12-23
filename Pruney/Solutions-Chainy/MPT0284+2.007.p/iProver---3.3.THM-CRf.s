%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:39 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
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

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f43,f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f43])).

fof(f11,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3))) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f27])).

fof(f44,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f43])).

fof(f52,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
    inference(definition_unfolding,[],[f44,f43,f45])).

cnf(c_179,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_181,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2247,plain,
    ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
    | r1_tarski(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_179,c_181])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6918,plain,
    ( ~ r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
    | r1_tarski(X3,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1))))
    | X3 != X0 ),
    inference(resolution,[status(thm)],[c_2247,c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_588,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) ),
    inference(resolution,[status(thm)],[c_2,c_11])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1290,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
    | ~ r1_tarski(sK0(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))),X2) ),
    inference(resolution,[status(thm)],[c_588,c_5])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_573,plain,
    ( r1_tarski(sK0(k1_zfmisc_1(X0),X1),X0)
    | r1_tarski(k1_zfmisc_1(X0),X1) ),
    inference(resolution,[status(thm)],[c_12,c_3])).

cnf(c_16299,plain,
    ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k3_tarski(k2_tarski(X1,X0)))) ),
    inference(resolution,[status(thm)],[c_1290,c_573])).

cnf(c_30855,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
    | X0 != k1_zfmisc_1(X1) ),
    inference(resolution,[status(thm)],[c_6918,c_16299])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1015,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK3,sK2)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2)))))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
    inference(resolution,[status(thm)],[c_8,c_13])).

cnf(c_16648,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_16299,c_1015])).

cnf(c_30914,plain,
    ( k1_zfmisc_1(k4_xboole_0(sK2,sK3)) != k1_zfmisc_1(k4_xboole_0(sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_30855,c_16648])).

cnf(c_30915,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_30914])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:54:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.94/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/1.49  
% 7.94/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.94/1.49  
% 7.94/1.49  ------  iProver source info
% 7.94/1.49  
% 7.94/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.94/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.94/1.49  git: non_committed_changes: false
% 7.94/1.49  git: last_make_outside_of_git: false
% 7.94/1.49  
% 7.94/1.49  ------ 
% 7.94/1.49  ------ Parsing...
% 7.94/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.94/1.49  
% 7.94/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.94/1.49  
% 7.94/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.94/1.49  
% 7.94/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.49  ------ Proving...
% 7.94/1.49  ------ Problem Properties 
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  clauses                                 14
% 7.94/1.49  conjectures                             1
% 7.94/1.49  EPR                                     1
% 7.94/1.49  Horn                                    12
% 7.94/1.49  unary                                   4
% 7.94/1.49  binary                                  6
% 7.94/1.49  lits                                    28
% 7.94/1.49  lits eq                                 5
% 7.94/1.49  fd_pure                                 0
% 7.94/1.49  fd_pseudo                               0
% 7.94/1.49  fd_cond                                 0
% 7.94/1.49  fd_pseudo_cond                          2
% 7.94/1.49  AC symbols                              0
% 7.94/1.49  
% 7.94/1.49  ------ Input Options Time Limit: Unbounded
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  ------ 
% 7.94/1.49  Current options:
% 7.94/1.49  ------ 
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  ------ Proving...
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  % SZS status Theorem for theBenchmark.p
% 7.94/1.49  
% 7.94/1.49   Resolution empty clause
% 7.94/1.49  
% 7.94/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.94/1.49  
% 7.94/1.49  fof(f1,axiom,(
% 7.94/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f29,plain,(
% 7.94/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f1])).
% 7.94/1.49  
% 7.94/1.49  fof(f10,axiom,(
% 7.94/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f43,plain,(
% 7.94/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.94/1.49    inference(cnf_transformation,[],[f10])).
% 7.94/1.49  
% 7.94/1.49  fof(f47,plain,(
% 7.94/1.49    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 7.94/1.49    inference(definition_unfolding,[],[f29,f43,f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f2,axiom,(
% 7.94/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f13,plain,(
% 7.94/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.94/1.49    inference(ennf_transformation,[],[f2])).
% 7.94/1.49  
% 7.94/1.49  fof(f19,plain,(
% 7.94/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.94/1.49    inference(nnf_transformation,[],[f13])).
% 7.94/1.49  
% 7.94/1.49  fof(f20,plain,(
% 7.94/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.94/1.49    inference(rectify,[],[f19])).
% 7.94/1.49  
% 7.94/1.49  fof(f21,plain,(
% 7.94/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.94/1.49    introduced(choice_axiom,[])).
% 7.94/1.49  
% 7.94/1.49  fof(f22,plain,(
% 7.94/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.94/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 7.94/1.49  
% 7.94/1.49  fof(f32,plain,(
% 7.94/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f22])).
% 7.94/1.49  
% 7.94/1.49  fof(f9,axiom,(
% 7.94/1.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f23,plain,(
% 7.94/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.94/1.49    inference(nnf_transformation,[],[f9])).
% 7.94/1.49  
% 7.94/1.49  fof(f24,plain,(
% 7.94/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.94/1.49    inference(rectify,[],[f23])).
% 7.94/1.49  
% 7.94/1.49  fof(f25,plain,(
% 7.94/1.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 7.94/1.49    introduced(choice_axiom,[])).
% 7.94/1.49  
% 7.94/1.49  fof(f26,plain,(
% 7.94/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.94/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 7.94/1.49  
% 7.94/1.49  fof(f40,plain,(
% 7.94/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.94/1.49    inference(cnf_transformation,[],[f26])).
% 7.94/1.49  
% 7.94/1.49  fof(f53,plain,(
% 7.94/1.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.94/1.49    inference(equality_resolution,[],[f40])).
% 7.94/1.49  
% 7.94/1.49  fof(f5,axiom,(
% 7.94/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f14,plain,(
% 7.94/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.94/1.49    inference(ennf_transformation,[],[f5])).
% 7.94/1.49  
% 7.94/1.49  fof(f35,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f14])).
% 7.94/1.49  
% 7.94/1.49  fof(f48,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 7.94/1.49    inference(definition_unfolding,[],[f35,f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f39,plain,(
% 7.94/1.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.94/1.49    inference(cnf_transformation,[],[f26])).
% 7.94/1.49  
% 7.94/1.49  fof(f54,plain,(
% 7.94/1.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.94/1.49    inference(equality_resolution,[],[f39])).
% 7.94/1.49  
% 7.94/1.49  fof(f31,plain,(
% 7.94/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f22])).
% 7.94/1.49  
% 7.94/1.49  fof(f8,axiom,(
% 7.94/1.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 7.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f16,plain,(
% 7.94/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 7.94/1.49    inference(ennf_transformation,[],[f8])).
% 7.94/1.49  
% 7.94/1.49  fof(f17,plain,(
% 7.94/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 7.94/1.49    inference(flattening,[],[f16])).
% 7.94/1.49  
% 7.94/1.49  fof(f38,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f17])).
% 7.94/1.49  
% 7.94/1.49  fof(f51,plain,(
% 7.94/1.49    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 7.94/1.49    inference(definition_unfolding,[],[f38,f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f11,conjecture,(
% 7.94/1.49    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 7.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f12,negated_conjecture,(
% 7.94/1.49    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 7.94/1.49    inference(negated_conjecture,[],[f11])).
% 7.94/1.49  
% 7.94/1.49  fof(f18,plain,(
% 7.94/1.49    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 7.94/1.49    inference(ennf_transformation,[],[f12])).
% 7.94/1.49  
% 7.94/1.49  fof(f27,plain,(
% 7.94/1.49    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3)))),
% 7.94/1.49    introduced(choice_axiom,[])).
% 7.94/1.49  
% 7.94/1.49  fof(f28,plain,(
% 7.94/1.49    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3)))),
% 7.94/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f18,f27])).
% 7.94/1.49  
% 7.94/1.49  fof(f44,plain,(
% 7.94/1.49    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2))),k1_zfmisc_1(k5_xboole_0(sK2,sK3)))),
% 7.94/1.49    inference(cnf_transformation,[],[f28])).
% 7.94/1.49  
% 7.94/1.49  fof(f3,axiom,(
% 7.94/1.49    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 7.94/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.94/1.49  
% 7.94/1.49  fof(f33,plain,(
% 7.94/1.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 7.94/1.49    inference(cnf_transformation,[],[f3])).
% 7.94/1.49  
% 7.94/1.49  fof(f45,plain,(
% 7.94/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 7.94/1.49    inference(definition_unfolding,[],[f33,f43])).
% 7.94/1.49  
% 7.94/1.49  fof(f52,plain,(
% 7.94/1.49    ~r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2)))))),
% 7.94/1.49    inference(definition_unfolding,[],[f44,f43,f45])).
% 7.94/1.49  
% 7.94/1.49  cnf(c_179,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.94/1.49      theory(equality) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_181,plain,
% 7.94/1.49      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.94/1.49      theory(equality) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2247,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,k1_zfmisc_1(X1))
% 7.94/1.49      | r1_tarski(X2,k1_zfmisc_1(X3))
% 7.94/1.49      | X2 != X0
% 7.94/1.49      | X3 != X1 ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_179,c_181]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1,plain,
% 7.94/1.49      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 7.94/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_6918,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
% 7.94/1.49      | r1_tarski(X3,k1_zfmisc_1(k3_tarski(k2_tarski(X2,X1))))
% 7.94/1.49      | X3 != X0 ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_2247,c_1]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_2,plain,
% 7.94/1.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.94/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_11,plain,
% 7.94/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.94/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_588,plain,
% 7.94/1.49      ( r1_tarski(X0,k1_zfmisc_1(X1))
% 7.94/1.49      | ~ r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_2,c_11]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_5,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 7.94/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1290,plain,
% 7.94/1.49      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
% 7.94/1.49      | ~ r1_tarski(sK0(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2)))),X2) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_588,c_5]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_12,plain,
% 7.94/1.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.94/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_3,plain,
% 7.94/1.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.94/1.49      inference(cnf_transformation,[],[f31]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_573,plain,
% 7.94/1.49      ( r1_tarski(sK0(k1_zfmisc_1(X0),X1),X0) | r1_tarski(k1_zfmisc_1(X0),X1) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_12,c_3]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_16299,plain,
% 7.94/1.49      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k3_tarski(k2_tarski(X1,X0)))) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_1290,c_573]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_30855,plain,
% 7.94/1.49      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(k2_tarski(X1,X2))))
% 7.94/1.49      | X0 != k1_zfmisc_1(X1) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_6918,c_16299]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_8,plain,
% 7.94/1.49      ( ~ r1_tarski(X0,X1)
% 7.94/1.49      | ~ r1_tarski(X2,X1)
% 7.94/1.49      | r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) ),
% 7.94/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_13,negated_conjecture,
% 7.94/1.49      ( ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k4_xboole_0(sK3,sK2)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
% 7.94/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_1015,plain,
% 7.94/1.49      ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK3,sK2)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2)))))
% 7.94/1.49      | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_8,c_13]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_16648,plain,
% 7.94/1.49      ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK2,sK3)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK2,sK3),k4_xboole_0(sK3,sK2))))) ),
% 7.94/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_16299,c_1015]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_30914,plain,
% 7.94/1.49      ( k1_zfmisc_1(k4_xboole_0(sK2,sK3)) != k1_zfmisc_1(k4_xboole_0(sK2,sK3)) ),
% 7.94/1.49      inference(resolution,[status(thm)],[c_30855,c_16648]) ).
% 7.94/1.49  
% 7.94/1.49  cnf(c_30915,plain,
% 7.94/1.49      ( $false ),
% 7.94/1.49      inference(equality_resolution_simp,[status(thm)],[c_30914]) ).
% 7.94/1.49  
% 7.94/1.49  
% 7.94/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.94/1.49  
% 7.94/1.49  ------                               Statistics
% 7.94/1.49  
% 7.94/1.49  ------ Selected
% 7.94/1.49  
% 7.94/1.49  total_time:                             0.92
% 7.94/1.49  
%------------------------------------------------------------------------------
