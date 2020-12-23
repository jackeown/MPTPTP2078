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
% DateTime   : Thu Dec  3 11:24:24 EST 2020

% Result     : Theorem 7.80s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :   71 (  87 expanded)
%              Number of clauses        :   39 (  44 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  146 ( 175 expanded)
%              Number of equality atoms :   92 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
      & r1_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    & r1_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f19])).

fof(f30,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK1(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f22,f28])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f31,plain,(
    k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f31,f28,f28])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_211,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( r2_xboole_0(k1_xboole_0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_212,plain,
    ( k1_xboole_0 = X0
    | r2_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_213,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_216,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1769,plain,
    ( r2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_213,c_216])).

cnf(c_26669,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_212,c_1769])).

cnf(c_27524,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_211,c_26669])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_27587,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_27524,c_6])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_27617,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_27587,c_4])).

cnf(c_76,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_804,plain,
    ( k4_xboole_0(sK2,sK4) = k4_xboole_0(X0,X1)
    | sK4 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_1190,plain,
    ( k4_xboole_0(sK2,sK4) = k4_xboole_0(X0,sK4)
    | sK4 != sK4
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_14587,plain,
    ( k4_xboole_0(sK2,sK4) = k4_xboole_0(k4_xboole_0(sK2,sK3),sK4)
    | sK4 != sK4
    | sK2 != k4_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1190])).

cnf(c_74,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1471,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,X3)
    | k4_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_12446,plain,
    ( k4_xboole_0(sK2,sK3) != X0
    | sK2 != X0
    | sK2 = k4_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_12447,plain,
    ( k4_xboole_0(sK2,sK3) != sK2
    | sK2 = k4_xboole_0(sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_12446])).

cnf(c_301,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != X0
    | k4_xboole_0(sK2,sK4) != X0
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_411,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(X0,X1)
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(X0,X1)
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_301])).

cnf(c_3369,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(X0,sK4)
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(X0,sK4)
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_6377,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(k4_xboole_0(sK2,sK3),sK4)
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(k4_xboole_0(sK2,sK3),sK4)
    | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3369])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1163,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_410,plain,
    ( X0 != X1
    | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != X1
    | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_685,plain,
    ( X0 != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = X0
    | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_1162,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k4_xboole_0(k4_xboole_0(sK2,sK3),sK4)
    | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_685])).

cnf(c_73,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_663,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_487,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_295,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
    | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_76])).

cnf(c_86,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_8,negated_conjecture,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27617,c_14587,c_12447,c_6377,c_1163,c_1162,c_663,c_487,c_295,c_86,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.80/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.80/1.49  
% 7.80/1.49  ------  iProver source info
% 7.80/1.49  
% 7.80/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.80/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.80/1.49  git: non_committed_changes: false
% 7.80/1.49  git: last_make_outside_of_git: false
% 7.80/1.49  
% 7.80/1.49  ------ 
% 7.80/1.49  ------ Parsing...
% 7.80/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.80/1.49  
% 7.80/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.80/1.49  ------ Proving...
% 7.80/1.49  ------ Problem Properties 
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  clauses                                 10
% 7.80/1.49  conjectures                             2
% 7.80/1.49  EPR                                     2
% 7.80/1.49  Horn                                    8
% 7.80/1.49  unary                                   5
% 7.80/1.49  binary                                  5
% 7.80/1.49  lits                                    15
% 7.80/1.49  lits eq                                 5
% 7.80/1.49  fd_pure                                 0
% 7.80/1.49  fd_pseudo                               0
% 7.80/1.49  fd_cond                                 1
% 7.80/1.49  fd_pseudo_cond                          0
% 7.80/1.49  AC symbols                              0
% 7.80/1.49  
% 7.80/1.49  ------ Input Options Time Limit: Unbounded
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ 
% 7.80/1.49  Current options:
% 7.80/1.49  ------ 
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  ------ Proving...
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  % SZS status Theorem for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  fof(f8,conjecture,(
% 7.80/1.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f9,negated_conjecture,(
% 7.80/1.49    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 7.80/1.49    inference(negated_conjecture,[],[f8])).
% 7.80/1.49  
% 7.80/1.49  fof(f14,plain,(
% 7.80/1.49    ? [X0,X1,X2] : (k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 7.80/1.49    inference(ennf_transformation,[],[f9])).
% 7.80/1.49  
% 7.80/1.49  fof(f19,plain,(
% 7.80/1.49    ? [X0,X1,X2] : (k3_xboole_0(X0,X2) != k3_xboole_0(X0,k2_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) & r1_xboole_0(sK2,sK3))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f20,plain,(
% 7.80/1.49    k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4)) & r1_xboole_0(sK2,sK3)),
% 7.80/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f14,f19])).
% 7.80/1.49  
% 7.80/1.49  fof(f30,plain,(
% 7.80/1.49    r1_xboole_0(sK2,sK3)),
% 7.80/1.49    inference(cnf_transformation,[],[f20])).
% 7.80/1.49  
% 7.80/1.49  fof(f7,axiom,(
% 7.80/1.49    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f13,plain,(
% 7.80/1.49    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 7.80/1.49    inference(ennf_transformation,[],[f7])).
% 7.80/1.49  
% 7.80/1.49  fof(f29,plain,(
% 7.80/1.49    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 7.80/1.49    inference(cnf_transformation,[],[f13])).
% 7.80/1.49  
% 7.80/1.49  fof(f2,axiom,(
% 7.80/1.49    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f12,plain,(
% 7.80/1.49    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 7.80/1.49    inference(ennf_transformation,[],[f2])).
% 7.80/1.49  
% 7.80/1.49  fof(f17,plain,(
% 7.80/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1)))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f18,plain,(
% 7.80/1.49    ! [X0,X1] : ((~r2_hidden(sK1(X0,X1),X0) & r2_hidden(sK1(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 7.80/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f17])).
% 7.80/1.49  
% 7.80/1.49  fof(f23,plain,(
% 7.80/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f18])).
% 7.80/1.49  
% 7.80/1.49  fof(f1,axiom,(
% 7.80/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f10,plain,(
% 7.80/1.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 7.80/1.49    inference(rectify,[],[f1])).
% 7.80/1.49  
% 7.80/1.49  fof(f11,plain,(
% 7.80/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.80/1.49    inference(ennf_transformation,[],[f10])).
% 7.80/1.49  
% 7.80/1.49  fof(f15,plain,(
% 7.80/1.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 7.80/1.49    introduced(choice_axiom,[])).
% 7.80/1.49  
% 7.80/1.49  fof(f16,plain,(
% 7.80/1.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 7.80/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f15])).
% 7.80/1.49  
% 7.80/1.49  fof(f22,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 7.80/1.49    inference(cnf_transformation,[],[f16])).
% 7.80/1.49  
% 7.80/1.49  fof(f6,axiom,(
% 7.80/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f28,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.80/1.49    inference(cnf_transformation,[],[f6])).
% 7.80/1.49  
% 7.80/1.49  fof(f32,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f22,f28])).
% 7.80/1.49  
% 7.80/1.49  fof(f5,axiom,(
% 7.80/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f27,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.80/1.49    inference(cnf_transformation,[],[f5])).
% 7.80/1.49  
% 7.80/1.49  fof(f34,plain,(
% 7.80/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.80/1.49    inference(definition_unfolding,[],[f27,f28])).
% 7.80/1.49  
% 7.80/1.49  fof(f3,axiom,(
% 7.80/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f25,plain,(
% 7.80/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.80/1.49    inference(cnf_transformation,[],[f3])).
% 7.80/1.49  
% 7.80/1.49  fof(f4,axiom,(
% 7.80/1.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.80/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.80/1.49  
% 7.80/1.49  fof(f26,plain,(
% 7.80/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.80/1.49    inference(cnf_transformation,[],[f4])).
% 7.80/1.49  
% 7.80/1.49  fof(f31,plain,(
% 7.80/1.49    k3_xboole_0(sK2,sK4) != k3_xboole_0(sK2,k2_xboole_0(sK3,sK4))),
% 7.80/1.49    inference(cnf_transformation,[],[f20])).
% 7.80/1.49  
% 7.80/1.49  fof(f35,plain,(
% 7.80/1.49    k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))),
% 7.80/1.49    inference(definition_unfolding,[],[f31,f28,f28])).
% 7.80/1.49  
% 7.80/1.49  cnf(c_9,negated_conjecture,
% 7.80/1.49      ( r1_xboole_0(sK2,sK3) ),
% 7.80/1.49      inference(cnf_transformation,[],[f30]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_211,plain,
% 7.80/1.49      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_7,plain,
% 7.80/1.49      ( r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0 ),
% 7.80/1.49      inference(cnf_transformation,[],[f29]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_212,plain,
% 7.80/1.49      ( k1_xboole_0 = X0 | r2_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3,plain,
% 7.80/1.49      ( ~ r2_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 7.80/1.49      inference(cnf_transformation,[],[f23]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_213,plain,
% 7.80/1.49      ( r2_xboole_0(X0,X1) != iProver_top
% 7.80/1.49      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_0,plain,
% 7.80/1.49      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 7.80/1.49      | ~ r1_xboole_0(X1,X2) ),
% 7.80/1.49      inference(cnf_transformation,[],[f32]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_216,plain,
% 7.80/1.49      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 7.80/1.49      | r1_xboole_0(X1,X2) != iProver_top ),
% 7.80/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1769,plain,
% 7.80/1.49      ( r2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 7.80/1.49      | r1_xboole_0(X1,X2) != iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_213,c_216]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_26669,plain,
% 7.80/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.80/1.49      | r1_xboole_0(X0,X1) != iProver_top ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_212,c_1769]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_27524,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_211,c_26669]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_6,plain,
% 7.80/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.80/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_27587,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0) ),
% 7.80/1.49      inference(superposition,[status(thm)],[c_27524,c_6]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_4,plain,
% 7.80/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.80/1.49      inference(cnf_transformation,[],[f25]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_27617,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 7.80/1.49      inference(demodulation,[status(thm)],[c_27587,c_4]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_76,plain,
% 7.80/1.49      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 7.80/1.49      theory(equality) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_804,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,sK4) = k4_xboole_0(X0,X1)
% 7.80/1.49      | sK4 != X1
% 7.80/1.49      | sK2 != X0 ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_76]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1190,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,sK4) = k4_xboole_0(X0,sK4)
% 7.80/1.49      | sK4 != sK4
% 7.80/1.49      | sK2 != X0 ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_804]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_14587,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,sK4) = k4_xboole_0(k4_xboole_0(sK2,sK3),sK4)
% 7.80/1.49      | sK4 != sK4
% 7.80/1.49      | sK2 != k4_xboole_0(sK2,sK3) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_1190]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_74,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1471,plain,
% 7.80/1.49      ( X0 != X1 | X0 = k4_xboole_0(X2,X3) | k4_xboole_0(X2,X3) != X1 ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_74]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_12446,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,sK3) != X0
% 7.80/1.49      | sK2 != X0
% 7.80/1.49      | sK2 = k4_xboole_0(sK2,sK3) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_1471]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_12447,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,sK3) != sK2
% 7.80/1.49      | sK2 = k4_xboole_0(sK2,sK3)
% 7.80/1.49      | sK2 != sK2 ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_12446]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_301,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != X0
% 7.80/1.49      | k4_xboole_0(sK2,sK4) != X0
% 7.80/1.49      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_74]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_411,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(X0,X1)
% 7.80/1.49      | k4_xboole_0(sK2,sK4) != k4_xboole_0(X0,X1)
% 7.80/1.49      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_301]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_3369,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(X0,sK4)
% 7.80/1.49      | k4_xboole_0(sK2,sK4) != k4_xboole_0(X0,sK4)
% 7.80/1.49      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_411]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_6377,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(k4_xboole_0(sK2,sK3),sK4)
% 7.80/1.49      | k4_xboole_0(sK2,sK4) != k4_xboole_0(k4_xboole_0(sK2,sK3),sK4)
% 7.80/1.49      | k4_xboole_0(sK2,sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_3369]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_5,plain,
% 7.80/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.80/1.49      inference(cnf_transformation,[],[f26]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1163,plain,
% 7.80/1.49      ( k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_410,plain,
% 7.80/1.49      ( X0 != X1
% 7.80/1.49      | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != X1
% 7.80/1.49      | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = X0 ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_74]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_685,plain,
% 7.80/1.49      ( X0 != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))
% 7.80/1.49      | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = X0
% 7.80/1.49      | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_410]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_1162,plain,
% 7.80/1.49      ( k4_xboole_0(k4_xboole_0(sK2,sK3),sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))
% 7.80/1.49      | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k4_xboole_0(k4_xboole_0(sK2,sK3),sK4)
% 7.80/1.49      | k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_685]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_73,plain,( X0 = X0 ),theory(equality) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_663,plain,
% 7.80/1.49      ( sK4 = sK4 ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_73]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_487,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)) ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_73]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_295,plain,
% 7.80/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4)))
% 7.80/1.49      | k4_xboole_0(sK2,sK4) != k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))
% 7.80/1.49      | sK2 != sK2 ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_76]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_86,plain,
% 7.80/1.49      ( sK2 = sK2 ),
% 7.80/1.49      inference(instantiation,[status(thm)],[c_73]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(c_8,negated_conjecture,
% 7.80/1.49      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK3,sK4))) ),
% 7.80/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.80/1.49  
% 7.80/1.49  cnf(contradiction,plain,
% 7.80/1.49      ( $false ),
% 7.80/1.49      inference(minisat,
% 7.80/1.49                [status(thm)],
% 7.80/1.49                [c_27617,c_14587,c_12447,c_6377,c_1163,c_1162,c_663,
% 7.80/1.49                 c_487,c_295,c_86,c_8]) ).
% 7.80/1.49  
% 7.80/1.49  
% 7.80/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.80/1.49  
% 7.80/1.49  ------                               Statistics
% 7.80/1.49  
% 7.80/1.49  ------ Selected
% 7.80/1.49  
% 7.80/1.49  total_time:                             0.626
% 7.80/1.49  
%------------------------------------------------------------------------------
