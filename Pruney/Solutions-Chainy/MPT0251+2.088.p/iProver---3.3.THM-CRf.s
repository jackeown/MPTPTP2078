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
% DateTime   : Thu Dec  3 11:33:16 EST 2020

% Result     : Theorem 3.92s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 718 expanded)
%              Number of clauses        :   34 ( 120 expanded)
%              Number of leaves         :   15 ( 227 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 782 expanded)
%              Number of equality atoms :   75 ( 707 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_xboole_0(k1_tarski(sK0),sK1) != sK1
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).

fof(f45,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f44,f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f47,f47])).

fof(f46,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f60,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(definition_unfolding,[],[f46,f47,f50])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) ),
    inference(definition_unfolding,[],[f33,f47,f47,f30])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f34,f30,f30,f47])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12123,plain,
    ( r2_hidden(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_12126,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_12128,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12704,plain,
    ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12126,c_12128])).

cnf(c_15942,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,X0)
    | r2_hidden(X0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12123,c_12704])).

cnf(c_15999,plain,
    ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_12123,c_15942])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_12253,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != sK1 ),
    inference(demodulation,[status(thm)],[c_0,c_13])).

cnf(c_16019,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
    inference(demodulation,[status(thm)],[c_15999,c_12253])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12259,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_12325,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_12259,c_6])).

cnf(c_12326,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12325,c_12259])).

cnf(c_12469,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_12326,c_0])).

cnf(c_12328,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_12326,c_12259])).

cnf(c_8,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12127,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12323,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12259,c_12127])).

cnf(c_12365,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12323,c_12128])).

cnf(c_12474,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12469,c_12328,c_12365])).

cnf(c_12475,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_12474,c_12328])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12465,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_12326,c_7])).

cnf(c_12188,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_12127])).

cnf(c_12212,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_12188,c_12128])).

cnf(c_12480,plain,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_12465,c_12212,c_12328,c_12365])).

cnf(c_12481,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12480,c_12328])).

cnf(c_16020,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_16019,c_12475,c_12481])).

cnf(c_16021,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16020])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:18:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.92/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.92/0.99  
% 3.92/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.92/0.99  
% 3.92/0.99  ------  iProver source info
% 3.92/0.99  
% 3.92/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.92/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.92/0.99  git: non_committed_changes: false
% 3.92/0.99  git: last_make_outside_of_git: false
% 3.92/0.99  
% 3.92/0.99  ------ 
% 3.92/0.99  ------ Parsing...
% 3.92/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  ------ Proving...
% 3.92/0.99  ------ Problem Properties 
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  clauses                                 14
% 3.92/0.99  conjectures                             2
% 3.92/0.99  EPR                                     3
% 3.92/0.99  Horn                                    14
% 3.92/0.99  unary                                   9
% 3.92/0.99  binary                                  3
% 3.92/0.99  lits                                    21
% 3.92/0.99  lits eq                                 8
% 3.92/0.99  fd_pure                                 0
% 3.92/0.99  fd_pseudo                               0
% 3.92/0.99  fd_cond                                 0
% 3.92/0.99  fd_pseudo_cond                          1
% 3.92/0.99  AC symbols                              0
% 3.92/0.99  
% 3.92/0.99  ------ Input Options Time Limit: Unbounded
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.92/0.99  Current options:
% 3.92/0.99  ------ 
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/0.99  
% 3.92/0.99  ------ Proving...
% 3.92/0.99  
% 3.92/0.99  
% 3.92/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/1.00  
% 3.92/1.00  ------ Proving...
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/1.00  
% 3.92/1.00  ------ Proving...
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/1.00  
% 3.92/1.00  ------ Proving...
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.92/1.00  
% 3.92/1.00  ------ Proving...
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.92/1.00  
% 3.92/1.00  ------ Proving...
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  % SZS status Theorem for theBenchmark.p
% 3.92/1.00  
% 3.92/1.00   Resolution empty clause
% 3.92/1.00  
% 3.92/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.92/1.00  
% 3.92/1.00  fof(f16,conjecture,(
% 3.92/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f17,negated_conjecture,(
% 3.92/1.00    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 3.92/1.00    inference(negated_conjecture,[],[f16])).
% 3.92/1.00  
% 3.92/1.00  fof(f19,plain,(
% 3.92/1.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 3.92/1.00    inference(ennf_transformation,[],[f17])).
% 3.92/1.00  
% 3.92/1.00  fof(f24,plain,(
% 3.92/1.00    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1))),
% 3.92/1.00    introduced(choice_axiom,[])).
% 3.92/1.00  
% 3.92/1.00  fof(f25,plain,(
% 3.92/1.00    k2_xboole_0(k1_tarski(sK0),sK1) != sK1 & r2_hidden(sK0,sK1)),
% 3.92/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f24])).
% 3.92/1.00  
% 3.92/1.00  fof(f45,plain,(
% 3.92/1.00    r2_hidden(sK0,sK1)),
% 3.92/1.00    inference(cnf_transformation,[],[f25])).
% 3.92/1.00  
% 3.92/1.00  fof(f15,axiom,(
% 3.92/1.00    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f22,plain,(
% 3.92/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.92/1.00    inference(nnf_transformation,[],[f15])).
% 3.92/1.00  
% 3.92/1.00  fof(f23,plain,(
% 3.92/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.92/1.00    inference(flattening,[],[f22])).
% 3.92/1.00  
% 3.92/1.00  fof(f44,plain,(
% 3.92/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f23])).
% 3.92/1.00  
% 3.92/1.00  fof(f11,axiom,(
% 3.92/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f38,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f11])).
% 3.92/1.00  
% 3.92/1.00  fof(f12,axiom,(
% 3.92/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f39,plain,(
% 3.92/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f12])).
% 3.92/1.00  
% 3.92/1.00  fof(f13,axiom,(
% 3.92/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f40,plain,(
% 3.92/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f13])).
% 3.92/1.00  
% 3.92/1.00  fof(f48,plain,(
% 3.92/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.92/1.00    inference(definition_unfolding,[],[f39,f40])).
% 3.92/1.00  
% 3.92/1.00  fof(f49,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.92/1.00    inference(definition_unfolding,[],[f38,f48])).
% 3.92/1.00  
% 3.92/1.00  fof(f57,plain,(
% 3.92/1.00    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 3.92/1.00    inference(definition_unfolding,[],[f44,f49])).
% 3.92/1.00  
% 3.92/1.00  fof(f5,axiom,(
% 3.92/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f18,plain,(
% 3.92/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.92/1.00    inference(ennf_transformation,[],[f5])).
% 3.92/1.00  
% 3.92/1.00  fof(f32,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f18])).
% 3.92/1.00  
% 3.92/1.00  fof(f1,axiom,(
% 3.92/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f26,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f1])).
% 3.92/1.00  
% 3.92/1.00  fof(f9,axiom,(
% 3.92/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f36,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.92/1.00    inference(cnf_transformation,[],[f9])).
% 3.92/1.00  
% 3.92/1.00  fof(f3,axiom,(
% 3.92/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f30,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.92/1.00    inference(cnf_transformation,[],[f3])).
% 3.92/1.00  
% 3.92/1.00  fof(f47,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.92/1.00    inference(definition_unfolding,[],[f36,f30])).
% 3.92/1.00  
% 3.92/1.00  fof(f51,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.92/1.00    inference(definition_unfolding,[],[f26,f47,f47])).
% 3.92/1.00  
% 3.92/1.00  fof(f46,plain,(
% 3.92/1.00    k2_xboole_0(k1_tarski(sK0),sK1) != sK1),
% 3.92/1.00    inference(cnf_transformation,[],[f25])).
% 3.92/1.00  
% 3.92/1.00  fof(f10,axiom,(
% 3.92/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f37,plain,(
% 3.92/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f10])).
% 3.92/1.00  
% 3.92/1.00  fof(f50,plain,(
% 3.92/1.00    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.92/1.00    inference(definition_unfolding,[],[f37,f49])).
% 3.92/1.00  
% 3.92/1.00  fof(f60,plain,(
% 3.92/1.00    k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1),
% 3.92/1.00    inference(definition_unfolding,[],[f46,f47,f50])).
% 3.92/1.00  
% 3.92/1.00  fof(f4,axiom,(
% 3.92/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f31,plain,(
% 3.92/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.92/1.00    inference(cnf_transformation,[],[f4])).
% 3.92/1.00  
% 3.92/1.00  fof(f52,plain,(
% 3.92/1.00    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 3.92/1.00    inference(definition_unfolding,[],[f31,f47])).
% 3.92/1.00  
% 3.92/1.00  fof(f6,axiom,(
% 3.92/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f33,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.92/1.00    inference(cnf_transformation,[],[f6])).
% 3.92/1.00  
% 3.92/1.00  fof(f53,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0)))) )),
% 3.92/1.00    inference(definition_unfolding,[],[f33,f47,f47,f30])).
% 3.92/1.00  
% 3.92/1.00  fof(f8,axiom,(
% 3.92/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f35,plain,(
% 3.92/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.92/1.00    inference(cnf_transformation,[],[f8])).
% 3.92/1.00  
% 3.92/1.00  fof(f55,plain,(
% 3.92/1.00    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 3.92/1.00    inference(definition_unfolding,[],[f35,f47])).
% 3.92/1.00  
% 3.92/1.00  fof(f7,axiom,(
% 3.92/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.92/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.92/1.00  
% 3.92/1.00  fof(f34,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.92/1.00    inference(cnf_transformation,[],[f7])).
% 3.92/1.00  
% 3.92/1.00  fof(f54,plain,(
% 3.92/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 3.92/1.00    inference(definition_unfolding,[],[f34,f30,f30,f47])).
% 3.92/1.00  
% 3.92/1.00  cnf(c_14,negated_conjecture,
% 3.92/1.00      ( r2_hidden(sK0,sK1) ),
% 3.92/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12123,plain,
% 3.92/1.00      ( r2_hidden(sK0,sK1) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_10,plain,
% 3.92/1.00      ( ~ r2_hidden(X0,X1)
% 3.92/1.00      | ~ r2_hidden(X2,X1)
% 3.92/1.00      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) ),
% 3.92/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12126,plain,
% 3.92/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.92/1.00      | r2_hidden(X2,X1) != iProver_top
% 3.92/1.00      | r1_tarski(k3_enumset1(X2,X2,X2,X2,X0),X1) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_5,plain,
% 3.92/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.92/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12128,plain,
% 3.92/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12704,plain,
% 3.92/1.00      ( k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),X2) = k3_enumset1(X0,X0,X0,X0,X1)
% 3.92/1.00      | r2_hidden(X1,X2) != iProver_top
% 3.92/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_12126,c_12128]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_15942,plain,
% 3.92/1.00      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,X0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,X0)
% 3.92/1.00      | r2_hidden(X0,sK1) != iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_12123,c_12704]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_15999,plain,
% 3.92/1.00      ( k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_12123,c_15942]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_0,plain,
% 3.92/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.92/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_13,negated_conjecture,
% 3.92/1.00      ( k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k3_xboole_0(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))) != sK1 ),
% 3.92/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12253,plain,
% 3.92/1.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1))) != sK1 ),
% 3.92/1.00      inference(demodulation,[status(thm)],[c_0,c_13]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_16019,plain,
% 3.92/1.00      ( k5_xboole_0(sK1,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) != sK1 ),
% 3.92/1.00      inference(demodulation,[status(thm)],[c_15999,c_12253]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_4,plain,
% 3.92/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 3.92/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12259,plain,
% 3.92/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_6,plain,
% 3.92/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),k3_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X0)),X0))) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
% 3.92/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12325,plain,
% 3.92/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_12259,c_6]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12326,plain,
% 3.92/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 3.92/1.00      inference(light_normalisation,[status(thm)],[c_12325,c_12259]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12469,plain,
% 3.92/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_12326,c_0]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12328,plain,
% 3.92/1.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.92/1.00      inference(demodulation,[status(thm)],[c_12326,c_12259]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_8,plain,
% 3.92/1.00      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 3.92/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12127,plain,
% 3.92/1.00      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = iProver_top ),
% 3.92/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12323,plain,
% 3.92/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_12259,c_12127]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12365,plain,
% 3.92/1.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_12323,c_12128]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12474,plain,
% 3.92/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
% 3.92/1.00      inference(light_normalisation,[status(thm)],[c_12469,c_12328,c_12365]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12475,plain,
% 3.92/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.92/1.00      inference(demodulation,[status(thm)],[c_12474,c_12328]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_7,plain,
% 3.92/1.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.92/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12465,plain,
% 3.92/1.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_xboole_0(k5_xboole_0(k1_xboole_0,X0),X0)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_12326,c_7]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12188,plain,
% 3.92/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_4,c_12127]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12212,plain,
% 3.92/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.92/1.00      inference(superposition,[status(thm)],[c_12188,c_12128]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12480,plain,
% 3.92/1.00      ( k5_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.92/1.00      inference(light_normalisation,
% 3.92/1.00                [status(thm)],
% 3.92/1.00                [c_12465,c_12212,c_12328,c_12365]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_12481,plain,
% 3.92/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.92/1.00      inference(demodulation,[status(thm)],[c_12480,c_12328]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_16020,plain,
% 3.92/1.00      ( sK1 != sK1 ),
% 3.92/1.00      inference(demodulation,[status(thm)],[c_16019,c_12475,c_12481]) ).
% 3.92/1.00  
% 3.92/1.00  cnf(c_16021,plain,
% 3.92/1.00      ( $false ),
% 3.92/1.00      inference(equality_resolution_simp,[status(thm)],[c_16020]) ).
% 3.92/1.00  
% 3.92/1.00  
% 3.92/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.92/1.00  
% 3.92/1.00  ------                               Statistics
% 3.92/1.00  
% 3.92/1.00  ------ Selected
% 3.92/1.00  
% 3.92/1.00  total_time:                             0.383
% 3.92/1.00  
%------------------------------------------------------------------------------
