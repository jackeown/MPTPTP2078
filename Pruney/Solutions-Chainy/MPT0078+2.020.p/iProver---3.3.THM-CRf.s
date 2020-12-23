%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:43 EST 2020

% Result     : Theorem 19.30s
% Output     : CNFRefutation 19.30s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 364 expanded)
%              Number of clauses        :   54 ( 163 expanded)
%              Number of leaves         :   15 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  159 ( 690 expanded)
%              Number of equality atoms :   90 ( 357 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X2,X1)
          & r1_xboole_0(X0,X1)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_xboole_0(X2,X1)
      & r1_xboole_0(X0,X1)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f18])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
   => ( sK2 != sK4
      & r1_xboole_0(sK4,sK3)
      & r1_xboole_0(sK2,sK3)
      & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( sK2 != sK4
    & r1_xboole_0(sK4,sK3)
    & r1_xboole_0(sK2,sK3)
    & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f24])).

fof(f37,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f20])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f38,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    sK2 != sK4 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_337,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_13,negated_conjecture,
    ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_338,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_556,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_338])).

cnf(c_1409,plain,
    ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_556])).

cnf(c_1707,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_337,c_1409])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_339,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1821,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_1707,c_339])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_340,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_128,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_129,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
    inference(unflattening,[status(thm)],[c_128])).

cnf(c_334,plain,
    ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_129])).

cnf(c_1426,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_340,c_334])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_37406,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) ),
    inference(superposition,[status(thm)],[c_1426,c_5])).

cnf(c_504,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_337])).

cnf(c_616,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_504,c_338])).

cnf(c_945,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_616,c_339])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_554,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_337,c_338])).

cnf(c_844,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_554])).

cnf(c_947,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_844,c_339])).

cnf(c_941,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_504,c_339])).

cnf(c_4680,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_941])).

cnf(c_9718,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_947,c_4680])).

cnf(c_9721,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_9718,c_947])).

cnf(c_37413,plain,
    ( k4_xboole_0(sK2,sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_37406,c_945,c_9721])).

cnf(c_506,plain,
    ( r1_tarski(sK4,k2_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_337])).

cnf(c_1398,plain,
    ( r1_tarski(k4_xboole_0(sK4,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_506,c_556])).

cnf(c_1742,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sK3),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1398,c_339])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_119,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | sK3 != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_120,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
    inference(unflattening,[status(thm)],[c_119])).

cnf(c_335,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_120])).

cnf(c_1425,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_340,c_335])).

cnf(c_35086,plain,
    ( k2_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK4,sK3),sK4) ),
    inference(superposition,[status(thm)],[c_1425,c_5])).

cnf(c_35094,plain,
    ( k4_xboole_0(sK4,sK3) = sK4 ),
    inference(demodulation,[status(thm)],[c_35086,c_945,c_9721])).

cnf(c_61867,plain,
    ( k2_xboole_0(sK4,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1742,c_1742,c_35094])).

cnf(c_61952,plain,
    ( k2_xboole_0(sK2,sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_61867,c_0])).

cnf(c_62072,plain,
    ( sK4 = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1821,c_1821,c_37413,c_61952])).

cnf(c_199,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_350,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_199])).

cnf(c_40590,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_198,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_551,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_198])).

cnf(c_10,negated_conjecture,
    ( sK2 != sK4 ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62072,c_40590,c_551,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:19:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.30/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.30/2.99  
% 19.30/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.30/2.99  
% 19.30/2.99  ------  iProver source info
% 19.30/2.99  
% 19.30/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.30/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.30/2.99  git: non_committed_changes: false
% 19.30/2.99  git: last_make_outside_of_git: false
% 19.30/2.99  
% 19.30/2.99  ------ 
% 19.30/2.99  
% 19.30/2.99  ------ Input Options
% 19.30/2.99  
% 19.30/2.99  --out_options                           all
% 19.30/2.99  --tptp_safe_out                         true
% 19.30/2.99  --problem_path                          ""
% 19.30/2.99  --include_path                          ""
% 19.30/2.99  --clausifier                            res/vclausify_rel
% 19.30/2.99  --clausifier_options                    ""
% 19.30/2.99  --stdin                                 false
% 19.30/2.99  --stats_out                             all
% 19.30/2.99  
% 19.30/2.99  ------ General Options
% 19.30/2.99  
% 19.30/2.99  --fof                                   false
% 19.30/2.99  --time_out_real                         305.
% 19.30/2.99  --time_out_virtual                      -1.
% 19.30/2.99  --symbol_type_check                     false
% 19.30/2.99  --clausify_out                          false
% 19.30/2.99  --sig_cnt_out                           false
% 19.30/2.99  --trig_cnt_out                          false
% 19.30/2.99  --trig_cnt_out_tolerance                1.
% 19.30/2.99  --trig_cnt_out_sk_spl                   false
% 19.30/2.99  --abstr_cl_out                          false
% 19.30/2.99  
% 19.30/2.99  ------ Global Options
% 19.30/2.99  
% 19.30/2.99  --schedule                              default
% 19.30/2.99  --add_important_lit                     false
% 19.30/2.99  --prop_solver_per_cl                    1000
% 19.30/2.99  --min_unsat_core                        false
% 19.30/2.99  --soft_assumptions                      false
% 19.30/2.99  --soft_lemma_size                       3
% 19.30/2.99  --prop_impl_unit_size                   0
% 19.30/2.99  --prop_impl_unit                        []
% 19.30/2.99  --share_sel_clauses                     true
% 19.30/2.99  --reset_solvers                         false
% 19.30/2.99  --bc_imp_inh                            [conj_cone]
% 19.30/2.99  --conj_cone_tolerance                   3.
% 19.30/2.99  --extra_neg_conj                        none
% 19.30/2.99  --large_theory_mode                     true
% 19.30/2.99  --prolific_symb_bound                   200
% 19.30/2.99  --lt_threshold                          2000
% 19.30/2.99  --clause_weak_htbl                      true
% 19.30/2.99  --gc_record_bc_elim                     false
% 19.30/2.99  
% 19.30/2.99  ------ Preprocessing Options
% 19.30/2.99  
% 19.30/2.99  --preprocessing_flag                    true
% 19.30/2.99  --time_out_prep_mult                    0.1
% 19.30/2.99  --splitting_mode                        input
% 19.30/2.99  --splitting_grd                         true
% 19.30/2.99  --splitting_cvd                         false
% 19.30/2.99  --splitting_cvd_svl                     false
% 19.30/2.99  --splitting_nvd                         32
% 19.30/2.99  --sub_typing                            true
% 19.30/2.99  --prep_gs_sim                           true
% 19.30/2.99  --prep_unflatten                        true
% 19.30/2.99  --prep_res_sim                          true
% 19.30/2.99  --prep_upred                            true
% 19.30/2.99  --prep_sem_filter                       exhaustive
% 19.30/2.99  --prep_sem_filter_out                   false
% 19.30/2.99  --pred_elim                             true
% 19.30/2.99  --res_sim_input                         true
% 19.30/2.99  --eq_ax_congr_red                       true
% 19.30/2.99  --pure_diseq_elim                       true
% 19.30/2.99  --brand_transform                       false
% 19.30/2.99  --non_eq_to_eq                          false
% 19.30/2.99  --prep_def_merge                        true
% 19.30/2.99  --prep_def_merge_prop_impl              false
% 19.30/2.99  --prep_def_merge_mbd                    true
% 19.30/2.99  --prep_def_merge_tr_red                 false
% 19.30/2.99  --prep_def_merge_tr_cl                  false
% 19.30/2.99  --smt_preprocessing                     true
% 19.30/2.99  --smt_ac_axioms                         fast
% 19.30/2.99  --preprocessed_out                      false
% 19.30/2.99  --preprocessed_stats                    false
% 19.30/2.99  
% 19.30/2.99  ------ Abstraction refinement Options
% 19.30/2.99  
% 19.30/2.99  --abstr_ref                             []
% 19.30/2.99  --abstr_ref_prep                        false
% 19.30/2.99  --abstr_ref_until_sat                   false
% 19.30/2.99  --abstr_ref_sig_restrict                funpre
% 19.30/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.30/2.99  --abstr_ref_under                       []
% 19.30/2.99  
% 19.30/2.99  ------ SAT Options
% 19.30/2.99  
% 19.30/2.99  --sat_mode                              false
% 19.30/2.99  --sat_fm_restart_options                ""
% 19.30/2.99  --sat_gr_def                            false
% 19.30/2.99  --sat_epr_types                         true
% 19.30/2.99  --sat_non_cyclic_types                  false
% 19.30/2.99  --sat_finite_models                     false
% 19.30/2.99  --sat_fm_lemmas                         false
% 19.30/2.99  --sat_fm_prep                           false
% 19.30/2.99  --sat_fm_uc_incr                        true
% 19.30/2.99  --sat_out_model                         small
% 19.30/2.99  --sat_out_clauses                       false
% 19.30/2.99  
% 19.30/2.99  ------ QBF Options
% 19.30/2.99  
% 19.30/2.99  --qbf_mode                              false
% 19.30/2.99  --qbf_elim_univ                         false
% 19.30/2.99  --qbf_dom_inst                          none
% 19.30/2.99  --qbf_dom_pre_inst                      false
% 19.30/2.99  --qbf_sk_in                             false
% 19.30/2.99  --qbf_pred_elim                         true
% 19.30/2.99  --qbf_split                             512
% 19.30/2.99  
% 19.30/2.99  ------ BMC1 Options
% 19.30/2.99  
% 19.30/2.99  --bmc1_incremental                      false
% 19.30/2.99  --bmc1_axioms                           reachable_all
% 19.30/2.99  --bmc1_min_bound                        0
% 19.30/2.99  --bmc1_max_bound                        -1
% 19.30/2.99  --bmc1_max_bound_default                -1
% 19.30/2.99  --bmc1_symbol_reachability              true
% 19.30/2.99  --bmc1_property_lemmas                  false
% 19.30/2.99  --bmc1_k_induction                      false
% 19.30/2.99  --bmc1_non_equiv_states                 false
% 19.30/2.99  --bmc1_deadlock                         false
% 19.30/2.99  --bmc1_ucm                              false
% 19.30/2.99  --bmc1_add_unsat_core                   none
% 19.30/2.99  --bmc1_unsat_core_children              false
% 19.30/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.30/2.99  --bmc1_out_stat                         full
% 19.30/2.99  --bmc1_ground_init                      false
% 19.30/2.99  --bmc1_pre_inst_next_state              false
% 19.30/2.99  --bmc1_pre_inst_state                   false
% 19.30/2.99  --bmc1_pre_inst_reach_state             false
% 19.30/2.99  --bmc1_out_unsat_core                   false
% 19.30/2.99  --bmc1_aig_witness_out                  false
% 19.30/2.99  --bmc1_verbose                          false
% 19.30/2.99  --bmc1_dump_clauses_tptp                false
% 19.30/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.30/2.99  --bmc1_dump_file                        -
% 19.30/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.30/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.30/2.99  --bmc1_ucm_extend_mode                  1
% 19.30/2.99  --bmc1_ucm_init_mode                    2
% 19.30/2.99  --bmc1_ucm_cone_mode                    none
% 19.30/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.30/2.99  --bmc1_ucm_relax_model                  4
% 19.30/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.30/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.30/2.99  --bmc1_ucm_layered_model                none
% 19.30/2.99  --bmc1_ucm_max_lemma_size               10
% 19.30/2.99  
% 19.30/2.99  ------ AIG Options
% 19.30/2.99  
% 19.30/2.99  --aig_mode                              false
% 19.30/2.99  
% 19.30/2.99  ------ Instantiation Options
% 19.30/2.99  
% 19.30/2.99  --instantiation_flag                    true
% 19.30/2.99  --inst_sos_flag                         true
% 19.30/2.99  --inst_sos_phase                        true
% 19.30/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.30/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.30/2.99  --inst_lit_sel_side                     num_symb
% 19.30/2.99  --inst_solver_per_active                1400
% 19.30/2.99  --inst_solver_calls_frac                1.
% 19.30/2.99  --inst_passive_queue_type               priority_queues
% 19.30/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.30/2.99  --inst_passive_queues_freq              [25;2]
% 19.30/2.99  --inst_dismatching                      true
% 19.30/2.99  --inst_eager_unprocessed_to_passive     true
% 19.30/2.99  --inst_prop_sim_given                   true
% 19.30/2.99  --inst_prop_sim_new                     false
% 19.30/2.99  --inst_subs_new                         false
% 19.30/2.99  --inst_eq_res_simp                      false
% 19.30/2.99  --inst_subs_given                       false
% 19.30/2.99  --inst_orphan_elimination               true
% 19.30/2.99  --inst_learning_loop_flag               true
% 19.30/2.99  --inst_learning_start                   3000
% 19.30/2.99  --inst_learning_factor                  2
% 19.30/2.99  --inst_start_prop_sim_after_learn       3
% 19.30/2.99  --inst_sel_renew                        solver
% 19.30/2.99  --inst_lit_activity_flag                true
% 19.30/2.99  --inst_restr_to_given                   false
% 19.30/2.99  --inst_activity_threshold               500
% 19.30/2.99  --inst_out_proof                        true
% 19.30/2.99  
% 19.30/2.99  ------ Resolution Options
% 19.30/2.99  
% 19.30/2.99  --resolution_flag                       true
% 19.30/2.99  --res_lit_sel                           adaptive
% 19.30/2.99  --res_lit_sel_side                      none
% 19.30/2.99  --res_ordering                          kbo
% 19.30/2.99  --res_to_prop_solver                    active
% 19.30/2.99  --res_prop_simpl_new                    false
% 19.30/2.99  --res_prop_simpl_given                  true
% 19.30/2.99  --res_passive_queue_type                priority_queues
% 19.30/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.30/2.99  --res_passive_queues_freq               [15;5]
% 19.30/2.99  --res_forward_subs                      full
% 19.30/2.99  --res_backward_subs                     full
% 19.30/2.99  --res_forward_subs_resolution           true
% 19.30/2.99  --res_backward_subs_resolution          true
% 19.30/2.99  --res_orphan_elimination                true
% 19.30/2.99  --res_time_limit                        2.
% 19.30/2.99  --res_out_proof                         true
% 19.30/2.99  
% 19.30/2.99  ------ Superposition Options
% 19.30/2.99  
% 19.30/2.99  --superposition_flag                    true
% 19.30/2.99  --sup_passive_queue_type                priority_queues
% 19.30/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.30/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.30/2.99  --demod_completeness_check              fast
% 19.30/2.99  --demod_use_ground                      true
% 19.30/2.99  --sup_to_prop_solver                    passive
% 19.30/2.99  --sup_prop_simpl_new                    true
% 19.30/2.99  --sup_prop_simpl_given                  true
% 19.30/2.99  --sup_fun_splitting                     true
% 19.30/2.99  --sup_smt_interval                      50000
% 19.30/2.99  
% 19.30/2.99  ------ Superposition Simplification Setup
% 19.30/2.99  
% 19.30/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.30/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.30/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.30/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.30/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.30/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.30/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.30/2.99  --sup_immed_triv                        [TrivRules]
% 19.30/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.99  --sup_immed_bw_main                     []
% 19.30/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.30/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.30/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.99  --sup_input_bw                          []
% 19.30/2.99  
% 19.30/2.99  ------ Combination Options
% 19.30/2.99  
% 19.30/2.99  --comb_res_mult                         3
% 19.30/2.99  --comb_sup_mult                         2
% 19.30/2.99  --comb_inst_mult                        10
% 19.30/2.99  
% 19.30/2.99  ------ Debug Options
% 19.30/2.99  
% 19.30/2.99  --dbg_backtrace                         false
% 19.30/2.99  --dbg_dump_prop_clauses                 false
% 19.30/2.99  --dbg_dump_prop_clauses_file            -
% 19.30/2.99  --dbg_out_stat                          false
% 19.30/2.99  ------ Parsing...
% 19.30/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.30/2.99  
% 19.30/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.30/2.99  
% 19.30/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.30/2.99  
% 19.30/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.30/2.99  ------ Proving...
% 19.30/2.99  ------ Problem Properties 
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  clauses                                 13
% 19.30/2.99  conjectures                             2
% 19.30/2.99  EPR                                     1
% 19.30/2.99  Horn                                    12
% 19.30/2.99  unary                                   9
% 19.30/2.99  binary                                  4
% 19.30/2.99  lits                                    17
% 19.30/2.99  lits eq                                 8
% 19.30/2.99  fd_pure                                 0
% 19.30/2.99  fd_pseudo                               0
% 19.30/2.99  fd_cond                                 1
% 19.30/2.99  fd_pseudo_cond                          0
% 19.30/2.99  AC symbols                              0
% 19.30/2.99  
% 19.30/2.99  ------ Schedule dynamic 5 is on 
% 19.30/2.99  
% 19.30/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  ------ 
% 19.30/2.99  Current options:
% 19.30/2.99  ------ 
% 19.30/2.99  
% 19.30/2.99  ------ Input Options
% 19.30/2.99  
% 19.30/2.99  --out_options                           all
% 19.30/2.99  --tptp_safe_out                         true
% 19.30/2.99  --problem_path                          ""
% 19.30/2.99  --include_path                          ""
% 19.30/2.99  --clausifier                            res/vclausify_rel
% 19.30/2.99  --clausifier_options                    ""
% 19.30/2.99  --stdin                                 false
% 19.30/2.99  --stats_out                             all
% 19.30/2.99  
% 19.30/2.99  ------ General Options
% 19.30/2.99  
% 19.30/2.99  --fof                                   false
% 19.30/2.99  --time_out_real                         305.
% 19.30/2.99  --time_out_virtual                      -1.
% 19.30/2.99  --symbol_type_check                     false
% 19.30/2.99  --clausify_out                          false
% 19.30/2.99  --sig_cnt_out                           false
% 19.30/2.99  --trig_cnt_out                          false
% 19.30/2.99  --trig_cnt_out_tolerance                1.
% 19.30/2.99  --trig_cnt_out_sk_spl                   false
% 19.30/2.99  --abstr_cl_out                          false
% 19.30/2.99  
% 19.30/2.99  ------ Global Options
% 19.30/2.99  
% 19.30/2.99  --schedule                              default
% 19.30/2.99  --add_important_lit                     false
% 19.30/2.99  --prop_solver_per_cl                    1000
% 19.30/2.99  --min_unsat_core                        false
% 19.30/2.99  --soft_assumptions                      false
% 19.30/2.99  --soft_lemma_size                       3
% 19.30/2.99  --prop_impl_unit_size                   0
% 19.30/2.99  --prop_impl_unit                        []
% 19.30/2.99  --share_sel_clauses                     true
% 19.30/2.99  --reset_solvers                         false
% 19.30/2.99  --bc_imp_inh                            [conj_cone]
% 19.30/2.99  --conj_cone_tolerance                   3.
% 19.30/2.99  --extra_neg_conj                        none
% 19.30/2.99  --large_theory_mode                     true
% 19.30/2.99  --prolific_symb_bound                   200
% 19.30/2.99  --lt_threshold                          2000
% 19.30/2.99  --clause_weak_htbl                      true
% 19.30/2.99  --gc_record_bc_elim                     false
% 19.30/2.99  
% 19.30/2.99  ------ Preprocessing Options
% 19.30/2.99  
% 19.30/2.99  --preprocessing_flag                    true
% 19.30/2.99  --time_out_prep_mult                    0.1
% 19.30/2.99  --splitting_mode                        input
% 19.30/2.99  --splitting_grd                         true
% 19.30/2.99  --splitting_cvd                         false
% 19.30/2.99  --splitting_cvd_svl                     false
% 19.30/2.99  --splitting_nvd                         32
% 19.30/2.99  --sub_typing                            true
% 19.30/2.99  --prep_gs_sim                           true
% 19.30/2.99  --prep_unflatten                        true
% 19.30/2.99  --prep_res_sim                          true
% 19.30/2.99  --prep_upred                            true
% 19.30/2.99  --prep_sem_filter                       exhaustive
% 19.30/2.99  --prep_sem_filter_out                   false
% 19.30/2.99  --pred_elim                             true
% 19.30/2.99  --res_sim_input                         true
% 19.30/2.99  --eq_ax_congr_red                       true
% 19.30/2.99  --pure_diseq_elim                       true
% 19.30/2.99  --brand_transform                       false
% 19.30/2.99  --non_eq_to_eq                          false
% 19.30/2.99  --prep_def_merge                        true
% 19.30/2.99  --prep_def_merge_prop_impl              false
% 19.30/2.99  --prep_def_merge_mbd                    true
% 19.30/2.99  --prep_def_merge_tr_red                 false
% 19.30/2.99  --prep_def_merge_tr_cl                  false
% 19.30/2.99  --smt_preprocessing                     true
% 19.30/2.99  --smt_ac_axioms                         fast
% 19.30/2.99  --preprocessed_out                      false
% 19.30/2.99  --preprocessed_stats                    false
% 19.30/2.99  
% 19.30/2.99  ------ Abstraction refinement Options
% 19.30/2.99  
% 19.30/2.99  --abstr_ref                             []
% 19.30/2.99  --abstr_ref_prep                        false
% 19.30/2.99  --abstr_ref_until_sat                   false
% 19.30/2.99  --abstr_ref_sig_restrict                funpre
% 19.30/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.30/2.99  --abstr_ref_under                       []
% 19.30/2.99  
% 19.30/2.99  ------ SAT Options
% 19.30/2.99  
% 19.30/2.99  --sat_mode                              false
% 19.30/2.99  --sat_fm_restart_options                ""
% 19.30/2.99  --sat_gr_def                            false
% 19.30/2.99  --sat_epr_types                         true
% 19.30/2.99  --sat_non_cyclic_types                  false
% 19.30/2.99  --sat_finite_models                     false
% 19.30/2.99  --sat_fm_lemmas                         false
% 19.30/2.99  --sat_fm_prep                           false
% 19.30/2.99  --sat_fm_uc_incr                        true
% 19.30/2.99  --sat_out_model                         small
% 19.30/2.99  --sat_out_clauses                       false
% 19.30/2.99  
% 19.30/2.99  ------ QBF Options
% 19.30/2.99  
% 19.30/2.99  --qbf_mode                              false
% 19.30/2.99  --qbf_elim_univ                         false
% 19.30/2.99  --qbf_dom_inst                          none
% 19.30/2.99  --qbf_dom_pre_inst                      false
% 19.30/2.99  --qbf_sk_in                             false
% 19.30/2.99  --qbf_pred_elim                         true
% 19.30/2.99  --qbf_split                             512
% 19.30/2.99  
% 19.30/2.99  ------ BMC1 Options
% 19.30/2.99  
% 19.30/2.99  --bmc1_incremental                      false
% 19.30/2.99  --bmc1_axioms                           reachable_all
% 19.30/2.99  --bmc1_min_bound                        0
% 19.30/2.99  --bmc1_max_bound                        -1
% 19.30/2.99  --bmc1_max_bound_default                -1
% 19.30/2.99  --bmc1_symbol_reachability              true
% 19.30/2.99  --bmc1_property_lemmas                  false
% 19.30/2.99  --bmc1_k_induction                      false
% 19.30/2.99  --bmc1_non_equiv_states                 false
% 19.30/2.99  --bmc1_deadlock                         false
% 19.30/2.99  --bmc1_ucm                              false
% 19.30/2.99  --bmc1_add_unsat_core                   none
% 19.30/2.99  --bmc1_unsat_core_children              false
% 19.30/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.30/2.99  --bmc1_out_stat                         full
% 19.30/2.99  --bmc1_ground_init                      false
% 19.30/2.99  --bmc1_pre_inst_next_state              false
% 19.30/2.99  --bmc1_pre_inst_state                   false
% 19.30/2.99  --bmc1_pre_inst_reach_state             false
% 19.30/2.99  --bmc1_out_unsat_core                   false
% 19.30/2.99  --bmc1_aig_witness_out                  false
% 19.30/2.99  --bmc1_verbose                          false
% 19.30/2.99  --bmc1_dump_clauses_tptp                false
% 19.30/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.30/2.99  --bmc1_dump_file                        -
% 19.30/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.30/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.30/2.99  --bmc1_ucm_extend_mode                  1
% 19.30/2.99  --bmc1_ucm_init_mode                    2
% 19.30/2.99  --bmc1_ucm_cone_mode                    none
% 19.30/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.30/2.99  --bmc1_ucm_relax_model                  4
% 19.30/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.30/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.30/2.99  --bmc1_ucm_layered_model                none
% 19.30/2.99  --bmc1_ucm_max_lemma_size               10
% 19.30/2.99  
% 19.30/2.99  ------ AIG Options
% 19.30/2.99  
% 19.30/2.99  --aig_mode                              false
% 19.30/2.99  
% 19.30/2.99  ------ Instantiation Options
% 19.30/2.99  
% 19.30/2.99  --instantiation_flag                    true
% 19.30/2.99  --inst_sos_flag                         true
% 19.30/2.99  --inst_sos_phase                        true
% 19.30/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.30/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.30/2.99  --inst_lit_sel_side                     none
% 19.30/2.99  --inst_solver_per_active                1400
% 19.30/2.99  --inst_solver_calls_frac                1.
% 19.30/2.99  --inst_passive_queue_type               priority_queues
% 19.30/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.30/2.99  --inst_passive_queues_freq              [25;2]
% 19.30/2.99  --inst_dismatching                      true
% 19.30/2.99  --inst_eager_unprocessed_to_passive     true
% 19.30/2.99  --inst_prop_sim_given                   true
% 19.30/2.99  --inst_prop_sim_new                     false
% 19.30/2.99  --inst_subs_new                         false
% 19.30/2.99  --inst_eq_res_simp                      false
% 19.30/2.99  --inst_subs_given                       false
% 19.30/2.99  --inst_orphan_elimination               true
% 19.30/2.99  --inst_learning_loop_flag               true
% 19.30/2.99  --inst_learning_start                   3000
% 19.30/2.99  --inst_learning_factor                  2
% 19.30/2.99  --inst_start_prop_sim_after_learn       3
% 19.30/2.99  --inst_sel_renew                        solver
% 19.30/2.99  --inst_lit_activity_flag                true
% 19.30/2.99  --inst_restr_to_given                   false
% 19.30/2.99  --inst_activity_threshold               500
% 19.30/2.99  --inst_out_proof                        true
% 19.30/2.99  
% 19.30/2.99  ------ Resolution Options
% 19.30/2.99  
% 19.30/2.99  --resolution_flag                       false
% 19.30/2.99  --res_lit_sel                           adaptive
% 19.30/2.99  --res_lit_sel_side                      none
% 19.30/2.99  --res_ordering                          kbo
% 19.30/2.99  --res_to_prop_solver                    active
% 19.30/2.99  --res_prop_simpl_new                    false
% 19.30/2.99  --res_prop_simpl_given                  true
% 19.30/2.99  --res_passive_queue_type                priority_queues
% 19.30/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.30/2.99  --res_passive_queues_freq               [15;5]
% 19.30/2.99  --res_forward_subs                      full
% 19.30/2.99  --res_backward_subs                     full
% 19.30/2.99  --res_forward_subs_resolution           true
% 19.30/2.99  --res_backward_subs_resolution          true
% 19.30/2.99  --res_orphan_elimination                true
% 19.30/2.99  --res_time_limit                        2.
% 19.30/2.99  --res_out_proof                         true
% 19.30/2.99  
% 19.30/2.99  ------ Superposition Options
% 19.30/2.99  
% 19.30/2.99  --superposition_flag                    true
% 19.30/2.99  --sup_passive_queue_type                priority_queues
% 19.30/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.30/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.30/2.99  --demod_completeness_check              fast
% 19.30/2.99  --demod_use_ground                      true
% 19.30/2.99  --sup_to_prop_solver                    passive
% 19.30/2.99  --sup_prop_simpl_new                    true
% 19.30/2.99  --sup_prop_simpl_given                  true
% 19.30/2.99  --sup_fun_splitting                     true
% 19.30/2.99  --sup_smt_interval                      50000
% 19.30/2.99  
% 19.30/2.99  ------ Superposition Simplification Setup
% 19.30/2.99  
% 19.30/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.30/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.30/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.30/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.30/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.30/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.30/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.30/2.99  --sup_immed_triv                        [TrivRules]
% 19.30/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.99  --sup_immed_bw_main                     []
% 19.30/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.30/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.30/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.30/2.99  --sup_input_bw                          []
% 19.30/2.99  
% 19.30/2.99  ------ Combination Options
% 19.30/2.99  
% 19.30/2.99  --comb_res_mult                         3
% 19.30/2.99  --comb_sup_mult                         2
% 19.30/2.99  --comb_inst_mult                        10
% 19.30/2.99  
% 19.30/2.99  ------ Debug Options
% 19.30/2.99  
% 19.30/2.99  --dbg_backtrace                         false
% 19.30/2.99  --dbg_dump_prop_clauses                 false
% 19.30/2.99  --dbg_dump_prop_clauses_file            -
% 19.30/2.99  --dbg_out_stat                          false
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  ------ Proving...
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  % SZS status Theorem for theBenchmark.p
% 19.30/2.99  
% 19.30/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.30/2.99  
% 19.30/2.99  fof(f10,axiom,(
% 19.30/2.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f36,plain,(
% 19.30/2.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 19.30/2.99    inference(cnf_transformation,[],[f10])).
% 19.30/2.99  
% 19.30/2.99  fof(f11,conjecture,(
% 19.30/2.99    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f12,negated_conjecture,(
% 19.30/2.99    ~! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 19.30/2.99    inference(negated_conjecture,[],[f11])).
% 19.30/2.99  
% 19.30/2.99  fof(f18,plain,(
% 19.30/2.99    ? [X0,X1,X2] : (X0 != X2 & (r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)))),
% 19.30/2.99    inference(ennf_transformation,[],[f12])).
% 19.30/2.99  
% 19.30/2.99  fof(f19,plain,(
% 19.30/2.99    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1))),
% 19.30/2.99    inference(flattening,[],[f18])).
% 19.30/2.99  
% 19.30/2.99  fof(f24,plain,(
% 19.30/2.99    ? [X0,X1,X2] : (X0 != X2 & r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => (sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3))),
% 19.30/2.99    introduced(choice_axiom,[])).
% 19.30/2.99  
% 19.30/2.99  fof(f25,plain,(
% 19.30/2.99    sK2 != sK4 & r1_xboole_0(sK4,sK3) & r1_xboole_0(sK2,sK3) & k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 19.30/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f24])).
% 19.30/2.99  
% 19.30/2.99  fof(f37,plain,(
% 19.30/2.99    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3)),
% 19.30/2.99    inference(cnf_transformation,[],[f25])).
% 19.30/2.99  
% 19.30/2.99  fof(f1,axiom,(
% 19.30/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f26,plain,(
% 19.30/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 19.30/2.99    inference(cnf_transformation,[],[f1])).
% 19.30/2.99  
% 19.30/2.99  fof(f7,axiom,(
% 19.30/2.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f17,plain,(
% 19.30/2.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 19.30/2.99    inference(ennf_transformation,[],[f7])).
% 19.30/2.99  
% 19.30/2.99  fof(f33,plain,(
% 19.30/2.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 19.30/2.99    inference(cnf_transformation,[],[f17])).
% 19.30/2.99  
% 19.30/2.99  fof(f4,axiom,(
% 19.30/2.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f16,plain,(
% 19.30/2.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 19.30/2.99    inference(ennf_transformation,[],[f4])).
% 19.30/2.99  
% 19.30/2.99  fof(f30,plain,(
% 19.30/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 19.30/2.99    inference(cnf_transformation,[],[f16])).
% 19.30/2.99  
% 19.30/2.99  fof(f3,axiom,(
% 19.30/2.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f15,plain,(
% 19.30/2.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 19.30/2.99    inference(ennf_transformation,[],[f3])).
% 19.30/2.99  
% 19.30/2.99  fof(f22,plain,(
% 19.30/2.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 19.30/2.99    introduced(choice_axiom,[])).
% 19.30/2.99  
% 19.30/2.99  fof(f23,plain,(
% 19.30/2.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 19.30/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).
% 19.30/2.99  
% 19.30/2.99  fof(f29,plain,(
% 19.30/2.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 19.30/2.99    inference(cnf_transformation,[],[f23])).
% 19.30/2.99  
% 19.30/2.99  fof(f2,axiom,(
% 19.30/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f13,plain,(
% 19.30/2.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 19.30/2.99    inference(rectify,[],[f2])).
% 19.30/2.99  
% 19.30/2.99  fof(f14,plain,(
% 19.30/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.30/2.99    inference(ennf_transformation,[],[f13])).
% 19.30/2.99  
% 19.30/2.99  fof(f20,plain,(
% 19.30/2.99    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 19.30/2.99    introduced(choice_axiom,[])).
% 19.30/2.99  
% 19.30/2.99  fof(f21,plain,(
% 19.30/2.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 19.30/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f20])).
% 19.30/2.99  
% 19.30/2.99  fof(f28,plain,(
% 19.30/2.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 19.30/2.99    inference(cnf_transformation,[],[f21])).
% 19.30/2.99  
% 19.30/2.99  fof(f9,axiom,(
% 19.30/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f35,plain,(
% 19.30/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.30/2.99    inference(cnf_transformation,[],[f9])).
% 19.30/2.99  
% 19.30/2.99  fof(f41,plain,(
% 19.30/2.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 19.30/2.99    inference(definition_unfolding,[],[f28,f35])).
% 19.30/2.99  
% 19.30/2.99  fof(f38,plain,(
% 19.30/2.99    r1_xboole_0(sK2,sK3)),
% 19.30/2.99    inference(cnf_transformation,[],[f25])).
% 19.30/2.99  
% 19.30/2.99  fof(f5,axiom,(
% 19.30/2.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f31,plain,(
% 19.30/2.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 19.30/2.99    inference(cnf_transformation,[],[f5])).
% 19.30/2.99  
% 19.30/2.99  fof(f6,axiom,(
% 19.30/2.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 19.30/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.30/2.99  
% 19.30/2.99  fof(f32,plain,(
% 19.30/2.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 19.30/2.99    inference(cnf_transformation,[],[f6])).
% 19.30/2.99  
% 19.30/2.99  fof(f39,plain,(
% 19.30/2.99    r1_xboole_0(sK4,sK3)),
% 19.30/2.99    inference(cnf_transformation,[],[f25])).
% 19.30/2.99  
% 19.30/2.99  fof(f40,plain,(
% 19.30/2.99    sK2 != sK4),
% 19.30/2.99    inference(cnf_transformation,[],[f25])).
% 19.30/2.99  
% 19.30/2.99  cnf(c_9,plain,
% 19.30/2.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 19.30/2.99      inference(cnf_transformation,[],[f36]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_337,plain,
% 19.30/2.99      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_13,negated_conjecture,
% 19.30/2.99      ( k2_xboole_0(sK2,sK3) = k2_xboole_0(sK4,sK3) ),
% 19.30/2.99      inference(cnf_transformation,[],[f37]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_0,plain,
% 19.30/2.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 19.30/2.99      inference(cnf_transformation,[],[f26]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_7,plain,
% 19.30/2.99      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 19.30/2.99      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 19.30/2.99      inference(cnf_transformation,[],[f33]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_338,plain,
% 19.30/2.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 19.30/2.99      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_556,plain,
% 19.30/2.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 19.30/2.99      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_0,c_338]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1409,plain,
% 19.30/2.99      ( r1_tarski(X0,k2_xboole_0(sK2,sK3)) != iProver_top
% 19.30/2.99      | r1_tarski(k4_xboole_0(X0,sK3),sK4) = iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_13,c_556]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1707,plain,
% 19.30/2.99      ( r1_tarski(k4_xboole_0(sK2,sK3),sK4) = iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_337,c_1409]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_4,plain,
% 19.30/2.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 19.30/2.99      inference(cnf_transformation,[],[f30]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_339,plain,
% 19.30/2.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1821,plain,
% 19.30/2.99      ( k2_xboole_0(k4_xboole_0(sK2,sK3),sK4) = sK4 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1707,c_339]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_3,plain,
% 19.30/2.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 19.30/2.99      inference(cnf_transformation,[],[f29]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_340,plain,
% 19.30/2.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1,plain,
% 19.30/2.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 19.30/2.99      | ~ r1_xboole_0(X1,X2) ),
% 19.30/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_12,negated_conjecture,
% 19.30/2.99      ( r1_xboole_0(sK2,sK3) ),
% 19.30/2.99      inference(cnf_transformation,[],[f38]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_128,plain,
% 19.30/2.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 19.30/2.99      | sK3 != X2
% 19.30/2.99      | sK2 != X1 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_1,c_12]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_129,plain,
% 19.30/2.99      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_128]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_334,plain,
% 19.30/2.99      ( r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_129]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1426,plain,
% 19.30/2.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_340,c_334]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_5,plain,
% 19.30/2.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 19.30/2.99      inference(cnf_transformation,[],[f31]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_37406,plain,
% 19.30/2.99      ( k2_xboole_0(k4_xboole_0(sK2,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK3),sK2) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1426,c_5]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_504,plain,
% 19.30/2.99      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_0,c_337]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_616,plain,
% 19.30/2.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_504,c_338]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_945,plain,
% 19.30/2.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_616,c_339]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_6,plain,
% 19.30/2.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.30/2.99      inference(cnf_transformation,[],[f32]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_554,plain,
% 19.30/2.99      ( r1_tarski(k4_xboole_0(X0,X0),X1) = iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_337,c_338]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_844,plain,
% 19.30/2.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_6,c_554]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_947,plain,
% 19.30/2.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_844,c_339]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_941,plain,
% 19.30/2.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_504,c_339]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_4680,plain,
% 19.30/2.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_0,c_941]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_9718,plain,
% 19.30/2.99      ( k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_947,c_4680]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_9721,plain,
% 19.30/2.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_9718,c_947]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_37413,plain,
% 19.30/2.99      ( k4_xboole_0(sK2,sK3) = sK2 ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_37406,c_945,c_9721]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_506,plain,
% 19.30/2.99      ( r1_tarski(sK4,k2_xboole_0(sK2,sK3)) = iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_13,c_337]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1398,plain,
% 19.30/2.99      ( r1_tarski(k4_xboole_0(sK4,sK3),sK2) = iProver_top ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_506,c_556]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1742,plain,
% 19.30/2.99      ( k2_xboole_0(k4_xboole_0(sK4,sK3),sK2) = sK2 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1398,c_339]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_11,negated_conjecture,
% 19.30/2.99      ( r1_xboole_0(sK4,sK3) ),
% 19.30/2.99      inference(cnf_transformation,[],[f39]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_119,plain,
% 19.30/2.99      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 19.30/2.99      | sK3 != X2
% 19.30/2.99      | sK4 != X1 ),
% 19.30/2.99      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_120,plain,
% 19.30/2.99      ( ~ r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
% 19.30/2.99      inference(unflattening,[status(thm)],[c_119]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_335,plain,
% 19.30/2.99      ( r2_hidden(X0,k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
% 19.30/2.99      inference(predicate_to_equality,[status(thm)],[c_120]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_1425,plain,
% 19.30/2.99      ( k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)) = k1_xboole_0 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_340,c_335]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_35086,plain,
% 19.30/2.99      ( k2_xboole_0(k4_xboole_0(sK4,sK3),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK4,sK3),sK4) ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_1425,c_5]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_35094,plain,
% 19.30/2.99      ( k4_xboole_0(sK4,sK3) = sK4 ),
% 19.30/2.99      inference(demodulation,[status(thm)],[c_35086,c_945,c_9721]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_61867,plain,
% 19.30/2.99      ( k2_xboole_0(sK4,sK2) = sK2 ),
% 19.30/2.99      inference(light_normalisation,
% 19.30/2.99                [status(thm)],
% 19.30/2.99                [c_1742,c_1742,c_35094]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_61952,plain,
% 19.30/2.99      ( k2_xboole_0(sK2,sK4) = sK2 ),
% 19.30/2.99      inference(superposition,[status(thm)],[c_61867,c_0]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_62072,plain,
% 19.30/2.99      ( sK4 = sK2 ),
% 19.30/2.99      inference(light_normalisation,
% 19.30/2.99                [status(thm)],
% 19.30/2.99                [c_1821,c_1821,c_37413,c_61952]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_199,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_350,plain,
% 19.30/2.99      ( sK4 != X0 | sK2 != X0 | sK2 = sK4 ),
% 19.30/2.99      inference(instantiation,[status(thm)],[c_199]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_40590,plain,
% 19.30/2.99      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 19.30/2.99      inference(instantiation,[status(thm)],[c_350]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_198,plain,( X0 = X0 ),theory(equality) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_551,plain,
% 19.30/2.99      ( sK2 = sK2 ),
% 19.30/2.99      inference(instantiation,[status(thm)],[c_198]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(c_10,negated_conjecture,
% 19.30/2.99      ( sK2 != sK4 ),
% 19.30/2.99      inference(cnf_transformation,[],[f40]) ).
% 19.30/2.99  
% 19.30/2.99  cnf(contradiction,plain,
% 19.30/2.99      ( $false ),
% 19.30/2.99      inference(minisat,[status(thm)],[c_62072,c_40590,c_551,c_10]) ).
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.30/2.99  
% 19.30/2.99  ------                               Statistics
% 19.30/2.99  
% 19.30/2.99  ------ General
% 19.30/2.99  
% 19.30/2.99  abstr_ref_over_cycles:                  0
% 19.30/2.99  abstr_ref_under_cycles:                 0
% 19.30/2.99  gc_basic_clause_elim:                   0
% 19.30/2.99  forced_gc_time:                         0
% 19.30/2.99  parsing_time:                           0.009
% 19.30/2.99  unif_index_cands_time:                  0.
% 19.30/2.99  unif_index_add_time:                    0.
% 19.30/2.99  orderings_time:                         0.
% 19.30/2.99  out_proof_time:                         0.011
% 19.30/2.99  total_time:                             2.142
% 19.30/2.99  num_of_symbols:                         42
% 19.30/2.99  num_of_terms:                           72282
% 19.30/2.99  
% 19.30/2.99  ------ Preprocessing
% 19.30/2.99  
% 19.30/2.99  num_of_splits:                          0
% 19.30/2.99  num_of_split_atoms:                     0
% 19.30/2.99  num_of_reused_defs:                     0
% 19.30/2.99  num_eq_ax_congr_red:                    10
% 19.30/2.99  num_of_sem_filtered_clauses:            1
% 19.30/2.99  num_of_subtypes:                        0
% 19.30/2.99  monotx_restored_types:                  0
% 19.30/2.99  sat_num_of_epr_types:                   0
% 19.30/2.99  sat_num_of_non_cyclic_types:            0
% 19.30/2.99  sat_guarded_non_collapsed_types:        0
% 19.30/2.99  num_pure_diseq_elim:                    0
% 19.30/2.99  simp_replaced_by:                       0
% 19.30/2.99  res_preprocessed:                       66
% 19.30/2.99  prep_upred:                             0
% 19.30/2.99  prep_unflattend:                        6
% 19.30/2.99  smt_new_axioms:                         0
% 19.30/2.99  pred_elim_cands:                        2
% 19.30/2.99  pred_elim:                              1
% 19.30/2.99  pred_elim_cl:                           1
% 19.30/2.99  pred_elim_cycles:                       3
% 19.30/2.99  merged_defs:                            0
% 19.30/2.99  merged_defs_ncl:                        0
% 19.30/2.99  bin_hyper_res:                          0
% 19.30/2.99  prep_cycles:                            4
% 19.30/2.99  pred_elim_time:                         0.
% 19.30/2.99  splitting_time:                         0.
% 19.30/2.99  sem_filter_time:                        0.
% 19.30/2.99  monotx_time:                            0.
% 19.30/2.99  subtype_inf_time:                       0.
% 19.30/2.99  
% 19.30/2.99  ------ Problem properties
% 19.30/2.99  
% 19.30/2.99  clauses:                                13
% 19.30/2.99  conjectures:                            2
% 19.30/2.99  epr:                                    1
% 19.30/2.99  horn:                                   12
% 19.30/2.99  ground:                                 2
% 19.30/2.99  unary:                                  9
% 19.30/2.99  binary:                                 4
% 19.30/2.99  lits:                                   17
% 19.30/2.99  lits_eq:                                8
% 19.30/2.99  fd_pure:                                0
% 19.30/2.99  fd_pseudo:                              0
% 19.30/2.99  fd_cond:                                1
% 19.30/2.99  fd_pseudo_cond:                         0
% 19.30/2.99  ac_symbols:                             0
% 19.30/2.99  
% 19.30/2.99  ------ Propositional Solver
% 19.30/2.99  
% 19.30/2.99  prop_solver_calls:                      40
% 19.30/2.99  prop_fast_solver_calls:                 712
% 19.30/2.99  smt_solver_calls:                       0
% 19.30/2.99  smt_fast_solver_calls:                  0
% 19.30/2.99  prop_num_of_clauses:                    25415
% 19.30/2.99  prop_preprocess_simplified:             27808
% 19.30/2.99  prop_fo_subsumed:                       0
% 19.30/2.99  prop_solver_time:                       0.
% 19.30/2.99  smt_solver_time:                        0.
% 19.30/2.99  smt_fast_solver_time:                   0.
% 19.30/2.99  prop_fast_solver_time:                  0.
% 19.30/2.99  prop_unsat_core_time:                   0.002
% 19.30/2.99  
% 19.30/2.99  ------ QBF
% 19.30/2.99  
% 19.30/2.99  qbf_q_res:                              0
% 19.30/2.99  qbf_num_tautologies:                    0
% 19.30/2.99  qbf_prep_cycles:                        0
% 19.30/2.99  
% 19.30/2.99  ------ BMC1
% 19.30/2.99  
% 19.30/2.99  bmc1_current_bound:                     -1
% 19.30/2.99  bmc1_last_solved_bound:                 -1
% 19.30/2.99  bmc1_unsat_core_size:                   -1
% 19.30/2.99  bmc1_unsat_core_parents_size:           -1
% 19.30/2.99  bmc1_merge_next_fun:                    0
% 19.30/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.30/2.99  
% 19.30/2.99  ------ Instantiation
% 19.30/2.99  
% 19.30/2.99  inst_num_of_clauses:                    7611
% 19.30/2.99  inst_num_in_passive:                    5128
% 19.30/2.99  inst_num_in_active:                     1748
% 19.30/2.99  inst_num_in_unprocessed:                735
% 19.30/2.99  inst_num_of_loops:                      2360
% 19.30/2.99  inst_num_of_learning_restarts:          0
% 19.30/2.99  inst_num_moves_active_passive:          605
% 19.30/2.99  inst_lit_activity:                      0
% 19.30/2.99  inst_lit_activity_moves:                1
% 19.30/2.99  inst_num_tautologies:                   0
% 19.30/2.99  inst_num_prop_implied:                  0
% 19.30/2.99  inst_num_existing_simplified:           0
% 19.30/2.99  inst_num_eq_res_simplified:             0
% 19.30/2.99  inst_num_child_elim:                    0
% 19.30/2.99  inst_num_of_dismatching_blockings:      6896
% 19.30/2.99  inst_num_of_non_proper_insts:           7897
% 19.30/2.99  inst_num_of_duplicates:                 0
% 19.30/2.99  inst_inst_num_from_inst_to_res:         0
% 19.30/2.99  inst_dismatching_checking_time:         0.
% 19.30/2.99  
% 19.30/2.99  ------ Resolution
% 19.30/2.99  
% 19.30/2.99  res_num_of_clauses:                     0
% 19.30/2.99  res_num_in_passive:                     0
% 19.30/2.99  res_num_in_active:                      0
% 19.30/2.99  res_num_of_loops:                       70
% 19.30/2.99  res_forward_subset_subsumed:            2768
% 19.30/2.99  res_backward_subset_subsumed:           0
% 19.30/2.99  res_forward_subsumed:                   0
% 19.30/2.99  res_backward_subsumed:                  0
% 19.30/2.99  res_forward_subsumption_resolution:     0
% 19.30/2.99  res_backward_subsumption_resolution:    0
% 19.30/2.99  res_clause_to_clause_subsumption:       115024
% 19.30/2.99  res_orphan_elimination:                 0
% 19.30/2.99  res_tautology_del:                      346
% 19.30/2.99  res_num_eq_res_simplified:              0
% 19.30/2.99  res_num_sel_changes:                    0
% 19.30/2.99  res_moves_from_active_to_pass:          0
% 19.30/2.99  
% 19.30/2.99  ------ Superposition
% 19.30/2.99  
% 19.30/2.99  sup_time_total:                         0.
% 19.30/2.99  sup_time_generating:                    0.
% 19.30/2.99  sup_time_sim_full:                      0.
% 19.30/2.99  sup_time_sim_immed:                     0.
% 19.30/2.99  
% 19.30/2.99  sup_num_of_clauses:                     5128
% 19.30/2.99  sup_num_in_active:                      464
% 19.30/2.99  sup_num_in_passive:                     4664
% 19.30/2.99  sup_num_of_loops:                       471
% 19.30/2.99  sup_fw_superposition:                   5888
% 19.30/2.99  sup_bw_superposition:                   5398
% 19.30/2.99  sup_immediate_simplified:               3219
% 19.30/2.99  sup_given_eliminated:                   2
% 19.30/2.99  comparisons_done:                       0
% 19.30/2.99  comparisons_avoided:                    0
% 19.30/2.99  
% 19.30/2.99  ------ Simplifications
% 19.30/2.99  
% 19.30/2.99  
% 19.30/2.99  sim_fw_subset_subsumed:                 3
% 19.30/2.99  sim_bw_subset_subsumed:                 0
% 19.30/2.99  sim_fw_subsumed:                        754
% 19.30/2.99  sim_bw_subsumed:                        49
% 19.30/2.99  sim_fw_subsumption_res:                 0
% 19.30/2.99  sim_bw_subsumption_res:                 0
% 19.30/2.99  sim_tautology_del:                      6
% 19.30/2.99  sim_eq_tautology_del:                   547
% 19.30/2.99  sim_eq_res_simp:                        0
% 19.30/2.99  sim_fw_demodulated:                     1222
% 19.30/2.99  sim_bw_demodulated:                     11
% 19.30/2.99  sim_light_normalised:                   1727
% 19.30/2.99  sim_joinable_taut:                      0
% 19.30/2.99  sim_joinable_simp:                      0
% 19.30/2.99  sim_ac_normalised:                      0
% 19.30/2.99  sim_smt_subsumption:                    0
% 19.30/2.99  
%------------------------------------------------------------------------------
