%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:10 EST 2020

% Result     : Theorem 55.37s
% Output     : CNFRefutation 55.37s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 532 expanded)
%              Number of clauses        :   49 ( 153 expanded)
%              Number of leaves         :   17 ( 158 expanded)
%              Depth                    :   20
%              Number of atoms          :  146 ( 585 expanded)
%              Number of equality atoms :   76 ( 503 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK4,sK2),k3_xboole_0(sK4,sK3))
      & r1_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK4,sK2),k3_xboole_0(sK4,sK3))
    & r1_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f27])).

fof(f44,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f25])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f23])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f39,f38,f38])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f38,f38])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f13,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK4,sK2),k3_xboole_0(sK4,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
    inference(definition_unfolding,[],[f45,f38,f38])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_299,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_303,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_305,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5237,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_303,c_305])).

cnf(c_149000,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_299,c_5237])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_764,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_1679,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_764])).

cnf(c_1768,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_1679,c_764])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_313,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_7])).

cnf(c_1770,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1768,c_313])).

cnf(c_1924,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1770,c_9])).

cnf(c_2377,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1924,c_8])).

cnf(c_2418,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2377,c_7])).

cnf(c_2590,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_2418])).

cnf(c_3492,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X0)))))) = X0 ),
    inference(superposition,[status(thm)],[c_9,c_2590])).

cnf(c_149443,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0)))) = sK3 ),
    inference(superposition,[status(thm)],[c_149000,c_3492])).

cnf(c_153984,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = sK3 ),
    inference(demodulation,[status(thm)],[c_149443,c_7])).

cnf(c_2612,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_2418,c_764])).

cnf(c_2634,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2612,c_7,c_313])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_301,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3001,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top
    | r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2634,c_301])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3016,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_2634,c_11])).

cnf(c_5,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_452,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_5])).

cnf(c_458,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_452,c_313])).

cnf(c_3021,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_3016,c_313,c_458])).

cnf(c_3056,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top
    | r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3001,c_3021])).

cnf(c_3059,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top
    | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3056,c_1770])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_302,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_306,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4919,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_302,c_306])).

cnf(c_63686,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3059,c_4919])).

cnf(c_63718,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2590,c_63686])).

cnf(c_158219,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k4_xboole_0(X1,k4_xboole_0(X1,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_153984,c_63718])).

cnf(c_14,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_300,plain,
    ( r1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_254160,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_158219,c_300])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 55.37/7.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.37/7.49  
% 55.37/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.37/7.49  
% 55.37/7.49  ------  iProver source info
% 55.37/7.49  
% 55.37/7.49  git: date: 2020-06-30 10:37:57 +0100
% 55.37/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.37/7.49  git: non_committed_changes: false
% 55.37/7.49  git: last_make_outside_of_git: false
% 55.37/7.49  
% 55.37/7.49  ------ 
% 55.37/7.49  
% 55.37/7.49  ------ Input Options
% 55.37/7.49  
% 55.37/7.49  --out_options                           all
% 55.37/7.49  --tptp_safe_out                         true
% 55.37/7.49  --problem_path                          ""
% 55.37/7.49  --include_path                          ""
% 55.37/7.49  --clausifier                            res/vclausify_rel
% 55.37/7.49  --clausifier_options                    --mode clausify
% 55.37/7.49  --stdin                                 false
% 55.37/7.49  --stats_out                             all
% 55.37/7.49  
% 55.37/7.49  ------ General Options
% 55.37/7.49  
% 55.37/7.49  --fof                                   false
% 55.37/7.49  --time_out_real                         305.
% 55.37/7.49  --time_out_virtual                      -1.
% 55.37/7.49  --symbol_type_check                     false
% 55.37/7.49  --clausify_out                          false
% 55.37/7.49  --sig_cnt_out                           false
% 55.37/7.50  --trig_cnt_out                          false
% 55.37/7.50  --trig_cnt_out_tolerance                1.
% 55.37/7.50  --trig_cnt_out_sk_spl                   false
% 55.37/7.50  --abstr_cl_out                          false
% 55.37/7.50  
% 55.37/7.50  ------ Global Options
% 55.37/7.50  
% 55.37/7.50  --schedule                              default
% 55.37/7.50  --add_important_lit                     false
% 55.37/7.50  --prop_solver_per_cl                    1000
% 55.37/7.50  --min_unsat_core                        false
% 55.37/7.50  --soft_assumptions                      false
% 55.37/7.50  --soft_lemma_size                       3
% 55.37/7.50  --prop_impl_unit_size                   0
% 55.37/7.50  --prop_impl_unit                        []
% 55.37/7.50  --share_sel_clauses                     true
% 55.37/7.50  --reset_solvers                         false
% 55.37/7.50  --bc_imp_inh                            [conj_cone]
% 55.37/7.50  --conj_cone_tolerance                   3.
% 55.37/7.50  --extra_neg_conj                        none
% 55.37/7.50  --large_theory_mode                     true
% 55.37/7.50  --prolific_symb_bound                   200
% 55.37/7.50  --lt_threshold                          2000
% 55.37/7.50  --clause_weak_htbl                      true
% 55.37/7.50  --gc_record_bc_elim                     false
% 55.37/7.50  
% 55.37/7.50  ------ Preprocessing Options
% 55.37/7.50  
% 55.37/7.50  --preprocessing_flag                    true
% 55.37/7.50  --time_out_prep_mult                    0.1
% 55.37/7.50  --splitting_mode                        input
% 55.37/7.50  --splitting_grd                         true
% 55.37/7.50  --splitting_cvd                         false
% 55.37/7.50  --splitting_cvd_svl                     false
% 55.37/7.50  --splitting_nvd                         32
% 55.37/7.50  --sub_typing                            true
% 55.37/7.50  --prep_gs_sim                           true
% 55.37/7.50  --prep_unflatten                        true
% 55.37/7.50  --prep_res_sim                          true
% 55.37/7.50  --prep_upred                            true
% 55.37/7.50  --prep_sem_filter                       exhaustive
% 55.37/7.50  --prep_sem_filter_out                   false
% 55.37/7.50  --pred_elim                             true
% 55.37/7.50  --res_sim_input                         true
% 55.37/7.50  --eq_ax_congr_red                       true
% 55.37/7.50  --pure_diseq_elim                       true
% 55.37/7.50  --brand_transform                       false
% 55.37/7.50  --non_eq_to_eq                          false
% 55.37/7.50  --prep_def_merge                        true
% 55.37/7.50  --prep_def_merge_prop_impl              false
% 55.37/7.50  --prep_def_merge_mbd                    true
% 55.37/7.50  --prep_def_merge_tr_red                 false
% 55.37/7.50  --prep_def_merge_tr_cl                  false
% 55.37/7.50  --smt_preprocessing                     true
% 55.37/7.50  --smt_ac_axioms                         fast
% 55.37/7.50  --preprocessed_out                      false
% 55.37/7.50  --preprocessed_stats                    false
% 55.37/7.50  
% 55.37/7.50  ------ Abstraction refinement Options
% 55.37/7.50  
% 55.37/7.50  --abstr_ref                             []
% 55.37/7.50  --abstr_ref_prep                        false
% 55.37/7.50  --abstr_ref_until_sat                   false
% 55.37/7.50  --abstr_ref_sig_restrict                funpre
% 55.37/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.37/7.50  --abstr_ref_under                       []
% 55.37/7.50  
% 55.37/7.50  ------ SAT Options
% 55.37/7.50  
% 55.37/7.50  --sat_mode                              false
% 55.37/7.50  --sat_fm_restart_options                ""
% 55.37/7.50  --sat_gr_def                            false
% 55.37/7.50  --sat_epr_types                         true
% 55.37/7.50  --sat_non_cyclic_types                  false
% 55.37/7.50  --sat_finite_models                     false
% 55.37/7.50  --sat_fm_lemmas                         false
% 55.37/7.50  --sat_fm_prep                           false
% 55.37/7.50  --sat_fm_uc_incr                        true
% 55.37/7.50  --sat_out_model                         small
% 55.37/7.50  --sat_out_clauses                       false
% 55.37/7.50  
% 55.37/7.50  ------ QBF Options
% 55.37/7.50  
% 55.37/7.50  --qbf_mode                              false
% 55.37/7.50  --qbf_elim_univ                         false
% 55.37/7.50  --qbf_dom_inst                          none
% 55.37/7.50  --qbf_dom_pre_inst                      false
% 55.37/7.50  --qbf_sk_in                             false
% 55.37/7.50  --qbf_pred_elim                         true
% 55.37/7.50  --qbf_split                             512
% 55.37/7.50  
% 55.37/7.50  ------ BMC1 Options
% 55.37/7.50  
% 55.37/7.50  --bmc1_incremental                      false
% 55.37/7.50  --bmc1_axioms                           reachable_all
% 55.37/7.50  --bmc1_min_bound                        0
% 55.37/7.50  --bmc1_max_bound                        -1
% 55.37/7.50  --bmc1_max_bound_default                -1
% 55.37/7.50  --bmc1_symbol_reachability              true
% 55.37/7.50  --bmc1_property_lemmas                  false
% 55.37/7.50  --bmc1_k_induction                      false
% 55.37/7.50  --bmc1_non_equiv_states                 false
% 55.37/7.50  --bmc1_deadlock                         false
% 55.37/7.50  --bmc1_ucm                              false
% 55.37/7.50  --bmc1_add_unsat_core                   none
% 55.37/7.50  --bmc1_unsat_core_children              false
% 55.37/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.37/7.50  --bmc1_out_stat                         full
% 55.37/7.50  --bmc1_ground_init                      false
% 55.37/7.50  --bmc1_pre_inst_next_state              false
% 55.37/7.50  --bmc1_pre_inst_state                   false
% 55.37/7.50  --bmc1_pre_inst_reach_state             false
% 55.37/7.50  --bmc1_out_unsat_core                   false
% 55.37/7.50  --bmc1_aig_witness_out                  false
% 55.37/7.50  --bmc1_verbose                          false
% 55.37/7.50  --bmc1_dump_clauses_tptp                false
% 55.37/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.37/7.50  --bmc1_dump_file                        -
% 55.37/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.37/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.37/7.50  --bmc1_ucm_extend_mode                  1
% 55.37/7.50  --bmc1_ucm_init_mode                    2
% 55.37/7.50  --bmc1_ucm_cone_mode                    none
% 55.37/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.37/7.50  --bmc1_ucm_relax_model                  4
% 55.37/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.37/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.37/7.50  --bmc1_ucm_layered_model                none
% 55.37/7.50  --bmc1_ucm_max_lemma_size               10
% 55.37/7.50  
% 55.37/7.50  ------ AIG Options
% 55.37/7.50  
% 55.37/7.50  --aig_mode                              false
% 55.37/7.50  
% 55.37/7.50  ------ Instantiation Options
% 55.37/7.50  
% 55.37/7.50  --instantiation_flag                    true
% 55.37/7.50  --inst_sos_flag                         false
% 55.37/7.50  --inst_sos_phase                        true
% 55.37/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.37/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.37/7.50  --inst_lit_sel_side                     num_symb
% 55.37/7.50  --inst_solver_per_active                1400
% 55.37/7.50  --inst_solver_calls_frac                1.
% 55.37/7.50  --inst_passive_queue_type               priority_queues
% 55.37/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.37/7.50  --inst_passive_queues_freq              [25;2]
% 55.37/7.50  --inst_dismatching                      true
% 55.37/7.50  --inst_eager_unprocessed_to_passive     true
% 55.37/7.50  --inst_prop_sim_given                   true
% 55.37/7.50  --inst_prop_sim_new                     false
% 55.37/7.50  --inst_subs_new                         false
% 55.37/7.50  --inst_eq_res_simp                      false
% 55.37/7.50  --inst_subs_given                       false
% 55.37/7.50  --inst_orphan_elimination               true
% 55.37/7.50  --inst_learning_loop_flag               true
% 55.37/7.50  --inst_learning_start                   3000
% 55.37/7.50  --inst_learning_factor                  2
% 55.37/7.50  --inst_start_prop_sim_after_learn       3
% 55.37/7.50  --inst_sel_renew                        solver
% 55.37/7.50  --inst_lit_activity_flag                true
% 55.37/7.50  --inst_restr_to_given                   false
% 55.37/7.50  --inst_activity_threshold               500
% 55.37/7.50  --inst_out_proof                        true
% 55.37/7.50  
% 55.37/7.50  ------ Resolution Options
% 55.37/7.50  
% 55.37/7.50  --resolution_flag                       true
% 55.37/7.50  --res_lit_sel                           adaptive
% 55.37/7.50  --res_lit_sel_side                      none
% 55.37/7.50  --res_ordering                          kbo
% 55.37/7.50  --res_to_prop_solver                    active
% 55.37/7.50  --res_prop_simpl_new                    false
% 55.37/7.50  --res_prop_simpl_given                  true
% 55.37/7.50  --res_passive_queue_type                priority_queues
% 55.37/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.37/7.50  --res_passive_queues_freq               [15;5]
% 55.37/7.50  --res_forward_subs                      full
% 55.37/7.50  --res_backward_subs                     full
% 55.37/7.50  --res_forward_subs_resolution           true
% 55.37/7.50  --res_backward_subs_resolution          true
% 55.37/7.50  --res_orphan_elimination                true
% 55.37/7.50  --res_time_limit                        2.
% 55.37/7.50  --res_out_proof                         true
% 55.37/7.50  
% 55.37/7.50  ------ Superposition Options
% 55.37/7.50  
% 55.37/7.50  --superposition_flag                    true
% 55.37/7.50  --sup_passive_queue_type                priority_queues
% 55.37/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.37/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.37/7.50  --demod_completeness_check              fast
% 55.37/7.50  --demod_use_ground                      true
% 55.37/7.50  --sup_to_prop_solver                    passive
% 55.37/7.50  --sup_prop_simpl_new                    true
% 55.37/7.50  --sup_prop_simpl_given                  true
% 55.37/7.50  --sup_fun_splitting                     false
% 55.37/7.50  --sup_smt_interval                      50000
% 55.37/7.50  
% 55.37/7.50  ------ Superposition Simplification Setup
% 55.37/7.50  
% 55.37/7.50  --sup_indices_passive                   []
% 55.37/7.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.37/7.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.37/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.37/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.37/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.37/7.50  --sup_full_bw                           [BwDemod]
% 55.37/7.50  --sup_immed_triv                        [TrivRules]
% 55.37/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.37/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.37/7.50  --sup_immed_bw_main                     []
% 55.37/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.37/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.37/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.37/7.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.37/7.50  
% 55.37/7.50  ------ Combination Options
% 55.37/7.50  
% 55.37/7.50  --comb_res_mult                         3
% 55.37/7.50  --comb_sup_mult                         2
% 55.37/7.50  --comb_inst_mult                        10
% 55.37/7.50  
% 55.37/7.50  ------ Debug Options
% 55.37/7.50  
% 55.37/7.50  --dbg_backtrace                         false
% 55.37/7.50  --dbg_dump_prop_clauses                 false
% 55.37/7.50  --dbg_dump_prop_clauses_file            -
% 55.37/7.50  --dbg_out_stat                          false
% 55.37/7.50  ------ Parsing...
% 55.37/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.37/7.50  
% 55.37/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 55.37/7.50  
% 55.37/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.37/7.50  
% 55.37/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.37/7.50  ------ Proving...
% 55.37/7.50  ------ Problem Properties 
% 55.37/7.50  
% 55.37/7.50  
% 55.37/7.50  clauses                                 16
% 55.37/7.50  conjectures                             2
% 55.37/7.50  EPR                                     3
% 55.37/7.50  Horn                                    14
% 55.37/7.50  unary                                   11
% 55.37/7.50  binary                                  5
% 55.37/7.50  lits                                    21
% 55.37/7.50  lits eq                                 9
% 55.37/7.50  fd_pure                                 0
% 55.37/7.50  fd_pseudo                               0
% 55.37/7.50  fd_cond                                 1
% 55.37/7.50  fd_pseudo_cond                          0
% 55.37/7.50  AC symbols                              0
% 55.37/7.50  
% 55.37/7.50  ------ Schedule dynamic 5 is on 
% 55.37/7.50  
% 55.37/7.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.37/7.50  
% 55.37/7.50  
% 55.37/7.50  ------ 
% 55.37/7.50  Current options:
% 55.37/7.50  ------ 
% 55.37/7.50  
% 55.37/7.50  ------ Input Options
% 55.37/7.50  
% 55.37/7.50  --out_options                           all
% 55.37/7.50  --tptp_safe_out                         true
% 55.37/7.50  --problem_path                          ""
% 55.37/7.50  --include_path                          ""
% 55.37/7.50  --clausifier                            res/vclausify_rel
% 55.37/7.50  --clausifier_options                    --mode clausify
% 55.37/7.50  --stdin                                 false
% 55.37/7.50  --stats_out                             all
% 55.37/7.50  
% 55.37/7.50  ------ General Options
% 55.37/7.50  
% 55.37/7.50  --fof                                   false
% 55.37/7.50  --time_out_real                         305.
% 55.37/7.50  --time_out_virtual                      -1.
% 55.37/7.50  --symbol_type_check                     false
% 55.37/7.50  --clausify_out                          false
% 55.37/7.50  --sig_cnt_out                           false
% 55.37/7.50  --trig_cnt_out                          false
% 55.37/7.50  --trig_cnt_out_tolerance                1.
% 55.37/7.50  --trig_cnt_out_sk_spl                   false
% 55.37/7.50  --abstr_cl_out                          false
% 55.37/7.50  
% 55.37/7.50  ------ Global Options
% 55.37/7.50  
% 55.37/7.50  --schedule                              default
% 55.37/7.50  --add_important_lit                     false
% 55.37/7.50  --prop_solver_per_cl                    1000
% 55.37/7.50  --min_unsat_core                        false
% 55.37/7.50  --soft_assumptions                      false
% 55.37/7.50  --soft_lemma_size                       3
% 55.37/7.50  --prop_impl_unit_size                   0
% 55.37/7.50  --prop_impl_unit                        []
% 55.37/7.50  --share_sel_clauses                     true
% 55.37/7.50  --reset_solvers                         false
% 55.37/7.50  --bc_imp_inh                            [conj_cone]
% 55.37/7.50  --conj_cone_tolerance                   3.
% 55.37/7.50  --extra_neg_conj                        none
% 55.37/7.50  --large_theory_mode                     true
% 55.37/7.50  --prolific_symb_bound                   200
% 55.37/7.50  --lt_threshold                          2000
% 55.37/7.50  --clause_weak_htbl                      true
% 55.37/7.50  --gc_record_bc_elim                     false
% 55.37/7.50  
% 55.37/7.50  ------ Preprocessing Options
% 55.37/7.50  
% 55.37/7.50  --preprocessing_flag                    true
% 55.37/7.50  --time_out_prep_mult                    0.1
% 55.37/7.50  --splitting_mode                        input
% 55.37/7.50  --splitting_grd                         true
% 55.37/7.50  --splitting_cvd                         false
% 55.37/7.50  --splitting_cvd_svl                     false
% 55.37/7.50  --splitting_nvd                         32
% 55.37/7.50  --sub_typing                            true
% 55.37/7.50  --prep_gs_sim                           true
% 55.37/7.50  --prep_unflatten                        true
% 55.37/7.50  --prep_res_sim                          true
% 55.37/7.50  --prep_upred                            true
% 55.37/7.50  --prep_sem_filter                       exhaustive
% 55.37/7.50  --prep_sem_filter_out                   false
% 55.37/7.50  --pred_elim                             true
% 55.37/7.50  --res_sim_input                         true
% 55.37/7.50  --eq_ax_congr_red                       true
% 55.37/7.50  --pure_diseq_elim                       true
% 55.37/7.50  --brand_transform                       false
% 55.37/7.50  --non_eq_to_eq                          false
% 55.37/7.50  --prep_def_merge                        true
% 55.37/7.50  --prep_def_merge_prop_impl              false
% 55.37/7.50  --prep_def_merge_mbd                    true
% 55.37/7.50  --prep_def_merge_tr_red                 false
% 55.37/7.50  --prep_def_merge_tr_cl                  false
% 55.37/7.50  --smt_preprocessing                     true
% 55.37/7.50  --smt_ac_axioms                         fast
% 55.37/7.50  --preprocessed_out                      false
% 55.37/7.50  --preprocessed_stats                    false
% 55.37/7.50  
% 55.37/7.50  ------ Abstraction refinement Options
% 55.37/7.50  
% 55.37/7.50  --abstr_ref                             []
% 55.37/7.50  --abstr_ref_prep                        false
% 55.37/7.50  --abstr_ref_until_sat                   false
% 55.37/7.50  --abstr_ref_sig_restrict                funpre
% 55.37/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.37/7.50  --abstr_ref_under                       []
% 55.37/7.50  
% 55.37/7.50  ------ SAT Options
% 55.37/7.50  
% 55.37/7.50  --sat_mode                              false
% 55.37/7.50  --sat_fm_restart_options                ""
% 55.37/7.50  --sat_gr_def                            false
% 55.37/7.50  --sat_epr_types                         true
% 55.37/7.50  --sat_non_cyclic_types                  false
% 55.37/7.50  --sat_finite_models                     false
% 55.37/7.50  --sat_fm_lemmas                         false
% 55.37/7.50  --sat_fm_prep                           false
% 55.37/7.50  --sat_fm_uc_incr                        true
% 55.37/7.50  --sat_out_model                         small
% 55.37/7.50  --sat_out_clauses                       false
% 55.37/7.50  
% 55.37/7.50  ------ QBF Options
% 55.37/7.50  
% 55.37/7.50  --qbf_mode                              false
% 55.37/7.50  --qbf_elim_univ                         false
% 55.37/7.50  --qbf_dom_inst                          none
% 55.37/7.50  --qbf_dom_pre_inst                      false
% 55.37/7.50  --qbf_sk_in                             false
% 55.37/7.50  --qbf_pred_elim                         true
% 55.37/7.50  --qbf_split                             512
% 55.37/7.50  
% 55.37/7.50  ------ BMC1 Options
% 55.37/7.50  
% 55.37/7.50  --bmc1_incremental                      false
% 55.37/7.50  --bmc1_axioms                           reachable_all
% 55.37/7.50  --bmc1_min_bound                        0
% 55.37/7.50  --bmc1_max_bound                        -1
% 55.37/7.50  --bmc1_max_bound_default                -1
% 55.37/7.50  --bmc1_symbol_reachability              true
% 55.37/7.50  --bmc1_property_lemmas                  false
% 55.37/7.50  --bmc1_k_induction                      false
% 55.37/7.50  --bmc1_non_equiv_states                 false
% 55.37/7.50  --bmc1_deadlock                         false
% 55.37/7.50  --bmc1_ucm                              false
% 55.37/7.50  --bmc1_add_unsat_core                   none
% 55.37/7.50  --bmc1_unsat_core_children              false
% 55.37/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.37/7.50  --bmc1_out_stat                         full
% 55.37/7.50  --bmc1_ground_init                      false
% 55.37/7.50  --bmc1_pre_inst_next_state              false
% 55.37/7.50  --bmc1_pre_inst_state                   false
% 55.37/7.50  --bmc1_pre_inst_reach_state             false
% 55.37/7.50  --bmc1_out_unsat_core                   false
% 55.37/7.50  --bmc1_aig_witness_out                  false
% 55.37/7.50  --bmc1_verbose                          false
% 55.37/7.50  --bmc1_dump_clauses_tptp                false
% 55.37/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.37/7.50  --bmc1_dump_file                        -
% 55.37/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.37/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.37/7.50  --bmc1_ucm_extend_mode                  1
% 55.37/7.50  --bmc1_ucm_init_mode                    2
% 55.37/7.50  --bmc1_ucm_cone_mode                    none
% 55.37/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.37/7.50  --bmc1_ucm_relax_model                  4
% 55.37/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.37/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.37/7.50  --bmc1_ucm_layered_model                none
% 55.37/7.50  --bmc1_ucm_max_lemma_size               10
% 55.37/7.50  
% 55.37/7.50  ------ AIG Options
% 55.37/7.50  
% 55.37/7.50  --aig_mode                              false
% 55.37/7.50  
% 55.37/7.50  ------ Instantiation Options
% 55.37/7.50  
% 55.37/7.50  --instantiation_flag                    true
% 55.37/7.50  --inst_sos_flag                         false
% 55.37/7.50  --inst_sos_phase                        true
% 55.37/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.37/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.37/7.50  --inst_lit_sel_side                     none
% 55.37/7.50  --inst_solver_per_active                1400
% 55.37/7.50  --inst_solver_calls_frac                1.
% 55.37/7.50  --inst_passive_queue_type               priority_queues
% 55.37/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.37/7.50  --inst_passive_queues_freq              [25;2]
% 55.37/7.50  --inst_dismatching                      true
% 55.37/7.50  --inst_eager_unprocessed_to_passive     true
% 55.37/7.50  --inst_prop_sim_given                   true
% 55.37/7.50  --inst_prop_sim_new                     false
% 55.37/7.50  --inst_subs_new                         false
% 55.37/7.50  --inst_eq_res_simp                      false
% 55.37/7.50  --inst_subs_given                       false
% 55.37/7.50  --inst_orphan_elimination               true
% 55.37/7.50  --inst_learning_loop_flag               true
% 55.37/7.50  --inst_learning_start                   3000
% 55.37/7.50  --inst_learning_factor                  2
% 55.37/7.50  --inst_start_prop_sim_after_learn       3
% 55.37/7.50  --inst_sel_renew                        solver
% 55.37/7.50  --inst_lit_activity_flag                true
% 55.37/7.50  --inst_restr_to_given                   false
% 55.37/7.50  --inst_activity_threshold               500
% 55.37/7.50  --inst_out_proof                        true
% 55.37/7.50  
% 55.37/7.50  ------ Resolution Options
% 55.37/7.50  
% 55.37/7.50  --resolution_flag                       false
% 55.37/7.50  --res_lit_sel                           adaptive
% 55.37/7.50  --res_lit_sel_side                      none
% 55.37/7.50  --res_ordering                          kbo
% 55.37/7.50  --res_to_prop_solver                    active
% 55.37/7.50  --res_prop_simpl_new                    false
% 55.37/7.50  --res_prop_simpl_given                  true
% 55.37/7.50  --res_passive_queue_type                priority_queues
% 55.37/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.37/7.50  --res_passive_queues_freq               [15;5]
% 55.37/7.50  --res_forward_subs                      full
% 55.37/7.50  --res_backward_subs                     full
% 55.37/7.50  --res_forward_subs_resolution           true
% 55.37/7.50  --res_backward_subs_resolution          true
% 55.37/7.50  --res_orphan_elimination                true
% 55.37/7.50  --res_time_limit                        2.
% 55.37/7.50  --res_out_proof                         true
% 55.37/7.50  
% 55.37/7.50  ------ Superposition Options
% 55.37/7.50  
% 55.37/7.50  --superposition_flag                    true
% 55.37/7.50  --sup_passive_queue_type                priority_queues
% 55.37/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.37/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.37/7.50  --demod_completeness_check              fast
% 55.37/7.50  --demod_use_ground                      true
% 55.37/7.50  --sup_to_prop_solver                    passive
% 55.37/7.50  --sup_prop_simpl_new                    true
% 55.37/7.50  --sup_prop_simpl_given                  true
% 55.37/7.50  --sup_fun_splitting                     false
% 55.37/7.50  --sup_smt_interval                      50000
% 55.37/7.50  
% 55.37/7.50  ------ Superposition Simplification Setup
% 55.37/7.50  
% 55.37/7.50  --sup_indices_passive                   []
% 55.37/7.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.37/7.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.37/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 55.37/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.37/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.37/7.50  --sup_full_bw                           [BwDemod]
% 55.37/7.50  --sup_immed_triv                        [TrivRules]
% 55.37/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.37/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.37/7.50  --sup_immed_bw_main                     []
% 55.37/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.37/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.37/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 55.37/7.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 55.37/7.50  
% 55.37/7.50  ------ Combination Options
% 55.37/7.50  
% 55.37/7.50  --comb_res_mult                         3
% 55.37/7.50  --comb_sup_mult                         2
% 55.37/7.50  --comb_inst_mult                        10
% 55.37/7.50  
% 55.37/7.50  ------ Debug Options
% 55.37/7.50  
% 55.37/7.50  --dbg_backtrace                         false
% 55.37/7.50  --dbg_dump_prop_clauses                 false
% 55.37/7.50  --dbg_dump_prop_clauses_file            -
% 55.37/7.50  --dbg_out_stat                          false
% 55.37/7.50  
% 55.37/7.50  
% 55.37/7.50  
% 55.37/7.50  
% 55.37/7.50  ------ Proving...
% 55.37/7.50  
% 55.37/7.50  
% 55.37/7.50  % SZS status Theorem for theBenchmark.p
% 55.37/7.50  
% 55.37/7.50   Resolution empty clause
% 55.37/7.50  
% 55.37/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.37/7.50  
% 55.37/7.50  fof(f15,conjecture,(
% 55.37/7.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f16,negated_conjecture,(
% 55.37/7.50    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 55.37/7.50    inference(negated_conjecture,[],[f15])).
% 55.37/7.50  
% 55.37/7.50  fof(f22,plain,(
% 55.37/7.50    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 55.37/7.50    inference(ennf_transformation,[],[f16])).
% 55.37/7.50  
% 55.37/7.50  fof(f27,plain,(
% 55.37/7.50    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK4,sK2),k3_xboole_0(sK4,sK3)) & r1_xboole_0(sK2,sK3))),
% 55.37/7.50    introduced(choice_axiom,[])).
% 55.37/7.50  
% 55.37/7.50  fof(f28,plain,(
% 55.37/7.50    ~r1_xboole_0(k3_xboole_0(sK4,sK2),k3_xboole_0(sK4,sK3)) & r1_xboole_0(sK2,sK3)),
% 55.37/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f27])).
% 55.37/7.50  
% 55.37/7.50  fof(f44,plain,(
% 55.37/7.50    r1_xboole_0(sK2,sK3)),
% 55.37/7.50    inference(cnf_transformation,[],[f28])).
% 55.37/7.50  
% 55.37/7.50  fof(f4,axiom,(
% 55.37/7.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f20,plain,(
% 55.37/7.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 55.37/7.50    inference(ennf_transformation,[],[f4])).
% 55.37/7.50  
% 55.37/7.50  fof(f25,plain,(
% 55.37/7.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 55.37/7.50    introduced(choice_axiom,[])).
% 55.37/7.50  
% 55.37/7.50  fof(f26,plain,(
% 55.37/7.50    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 55.37/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f25])).
% 55.37/7.50  
% 55.37/7.50  fof(f33,plain,(
% 55.37/7.50    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 55.37/7.50    inference(cnf_transformation,[],[f26])).
% 55.37/7.50  
% 55.37/7.50  fof(f3,axiom,(
% 55.37/7.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f17,plain,(
% 55.37/7.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 55.37/7.50    inference(rectify,[],[f3])).
% 55.37/7.50  
% 55.37/7.50  fof(f19,plain,(
% 55.37/7.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.37/7.50    inference(ennf_transformation,[],[f17])).
% 55.37/7.50  
% 55.37/7.50  fof(f23,plain,(
% 55.37/7.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 55.37/7.50    introduced(choice_axiom,[])).
% 55.37/7.50  
% 55.37/7.50  fof(f24,plain,(
% 55.37/7.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 55.37/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f23])).
% 55.37/7.50  
% 55.37/7.50  fof(f32,plain,(
% 55.37/7.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 55.37/7.50    inference(cnf_transformation,[],[f24])).
% 55.37/7.50  
% 55.37/7.50  fof(f9,axiom,(
% 55.37/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f38,plain,(
% 55.37/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 55.37/7.50    inference(cnf_transformation,[],[f9])).
% 55.37/7.50  
% 55.37/7.50  fof(f47,plain,(
% 55.37/7.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 55.37/7.50    inference(definition_unfolding,[],[f32,f38])).
% 55.37/7.50  
% 55.37/7.50  fof(f10,axiom,(
% 55.37/7.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f39,plain,(
% 55.37/7.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 55.37/7.50    inference(cnf_transformation,[],[f10])).
% 55.37/7.50  
% 55.37/7.50  fof(f52,plain,(
% 55.37/7.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 55.37/7.50    inference(definition_unfolding,[],[f39,f38,f38])).
% 55.37/7.50  
% 55.37/7.50  fof(f1,axiom,(
% 55.37/7.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f29,plain,(
% 55.37/7.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 55.37/7.50    inference(cnf_transformation,[],[f1])).
% 55.37/7.50  
% 55.37/7.50  fof(f46,plain,(
% 55.37/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 55.37/7.50    inference(definition_unfolding,[],[f29,f38,f38])).
% 55.37/7.50  
% 55.37/7.50  fof(f8,axiom,(
% 55.37/7.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f37,plain,(
% 55.37/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 55.37/7.50    inference(cnf_transformation,[],[f8])).
% 55.37/7.50  
% 55.37/7.50  fof(f51,plain,(
% 55.37/7.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 55.37/7.50    inference(definition_unfolding,[],[f37,f38])).
% 55.37/7.50  
% 55.37/7.50  fof(f6,axiom,(
% 55.37/7.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f35,plain,(
% 55.37/7.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 55.37/7.50    inference(cnf_transformation,[],[f6])).
% 55.37/7.50  
% 55.37/7.50  fof(f50,plain,(
% 55.37/7.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 55.37/7.50    inference(definition_unfolding,[],[f35,f38])).
% 55.37/7.50  
% 55.37/7.50  fof(f7,axiom,(
% 55.37/7.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f36,plain,(
% 55.37/7.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 55.37/7.50    inference(cnf_transformation,[],[f7])).
% 55.37/7.50  
% 55.37/7.50  fof(f14,axiom,(
% 55.37/7.50    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f21,plain,(
% 55.37/7.50    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 55.37/7.50    inference(ennf_transformation,[],[f14])).
% 55.37/7.50  
% 55.37/7.50  fof(f43,plain,(
% 55.37/7.50    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 55.37/7.50    inference(cnf_transformation,[],[f21])).
% 55.37/7.50  
% 55.37/7.50  fof(f55,plain,(
% 55.37/7.50    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 55.37/7.50    inference(definition_unfolding,[],[f43,f38])).
% 55.37/7.50  
% 55.37/7.50  fof(f12,axiom,(
% 55.37/7.50    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f41,plain,(
% 55.37/7.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 55.37/7.50    inference(cnf_transformation,[],[f12])).
% 55.37/7.50  
% 55.37/7.50  fof(f54,plain,(
% 55.37/7.50    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 55.37/7.50    inference(definition_unfolding,[],[f41,f38])).
% 55.37/7.50  
% 55.37/7.50  fof(f5,axiom,(
% 55.37/7.50    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f34,plain,(
% 55.37/7.50    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 55.37/7.50    inference(cnf_transformation,[],[f5])).
% 55.37/7.50  
% 55.37/7.50  fof(f49,plain,(
% 55.37/7.50    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 55.37/7.50    inference(definition_unfolding,[],[f34,f38])).
% 55.37/7.50  
% 55.37/7.50  fof(f13,axiom,(
% 55.37/7.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f42,plain,(
% 55.37/7.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 55.37/7.50    inference(cnf_transformation,[],[f13])).
% 55.37/7.50  
% 55.37/7.50  fof(f2,axiom,(
% 55.37/7.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 55.37/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.37/7.50  
% 55.37/7.50  fof(f18,plain,(
% 55.37/7.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 55.37/7.50    inference(ennf_transformation,[],[f2])).
% 55.37/7.50  
% 55.37/7.50  fof(f30,plain,(
% 55.37/7.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 55.37/7.50    inference(cnf_transformation,[],[f18])).
% 55.37/7.50  
% 55.37/7.50  fof(f45,plain,(
% 55.37/7.50    ~r1_xboole_0(k3_xboole_0(sK4,sK2),k3_xboole_0(sK4,sK3))),
% 55.37/7.50    inference(cnf_transformation,[],[f28])).
% 55.37/7.50  
% 55.37/7.50  fof(f56,plain,(
% 55.37/7.50    ~r1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK3)))),
% 55.37/7.50    inference(definition_unfolding,[],[f45,f38,f38])).
% 55.37/7.50  
% 55.37/7.50  cnf(c_15,negated_conjecture,
% 55.37/7.50      ( r1_xboole_0(sK2,sK3) ),
% 55.37/7.50      inference(cnf_transformation,[],[f44]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_299,plain,
% 55.37/7.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 55.37/7.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_4,plain,
% 55.37/7.50      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 55.37/7.50      inference(cnf_transformation,[],[f33]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_303,plain,
% 55.37/7.50      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 55.37/7.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_2,plain,
% 55.37/7.50      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 55.37/7.50      | ~ r1_xboole_0(X1,X2) ),
% 55.37/7.50      inference(cnf_transformation,[],[f47]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_305,plain,
% 55.37/7.50      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 55.37/7.50      | r1_xboole_0(X1,X2) != iProver_top ),
% 55.37/7.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_5237,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 55.37/7.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_303,c_305]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_149000,plain,
% 55.37/7.50      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)) = k1_xboole_0 ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_299,c_5237]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_9,plain,
% 55.37/7.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 55.37/7.50      inference(cnf_transformation,[],[f52]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_0,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 55.37/7.50      inference(cnf_transformation,[],[f46]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_8,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 55.37/7.50      inference(cnf_transformation,[],[f51]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_764,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_1679,plain,
% 55.37/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_0,c_764]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_1768,plain,
% 55.37/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 55.37/7.50      inference(light_normalisation,[status(thm)],[c_1679,c_764]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_6,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 55.37/7.50      inference(cnf_transformation,[],[f50]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_7,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.37/7.50      inference(cnf_transformation,[],[f36]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_313,plain,
% 55.37/7.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 55.37/7.50      inference(light_normalisation,[status(thm)],[c_6,c_7]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_1770,plain,
% 55.37/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 55.37/7.50      inference(demodulation,[status(thm)],[c_1768,c_313]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_1924,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_1770,c_9]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_2377,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_1924,c_8]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_2418,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 55.37/7.50      inference(light_normalisation,[status(thm)],[c_2377,c_7]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_2590,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = X0 ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_9,c_2418]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_3492,plain,
% 55.37/7.50      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X0)))))) = X0 ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_9,c_2590]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_149443,plain,
% 55.37/7.50      ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(sK2,k1_xboole_0)))) = sK3 ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_149000,c_3492]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_153984,plain,
% 55.37/7.50      ( k4_xboole_0(sK3,k4_xboole_0(X0,k4_xboole_0(X0,sK2))) = sK3 ),
% 55.37/7.50      inference(demodulation,[status(thm)],[c_149443,c_7]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_2612,plain,
% 55.37/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_2418,c_764]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_2634,plain,
% 55.37/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 55.37/7.50      inference(demodulation,[status(thm)],[c_2612,c_7,c_313]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_13,plain,
% 55.37/7.50      ( r1_xboole_0(X0,X1)
% 55.37/7.50      | ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) ),
% 55.37/7.50      inference(cnf_transformation,[],[f55]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_301,plain,
% 55.37/7.50      ( r1_xboole_0(X0,X1) = iProver_top
% 55.37/7.50      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 55.37/7.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_3001,plain,
% 55.37/7.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top
% 55.37/7.50      | r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X1) != iProver_top ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_2634,c_301]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_11,plain,
% 55.37/7.50      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 55.37/7.50      inference(cnf_transformation,[],[f54]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_3016,plain,
% 55.37/7.50      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_2634,c_11]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_5,plain,
% 55.37/7.50      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 55.37/7.50      inference(cnf_transformation,[],[f49]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_452,plain,
% 55.37/7.50      ( k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_7,c_5]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_458,plain,
% 55.37/7.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 55.37/7.50      inference(light_normalisation,[status(thm)],[c_452,c_313]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_3021,plain,
% 55.37/7.50      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 55.37/7.50      inference(demodulation,[status(thm)],[c_3016,c_313,c_458]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_3056,plain,
% 55.37/7.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top
% 55.37/7.50      | r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X1) != iProver_top ),
% 55.37/7.50      inference(demodulation,[status(thm)],[c_3001,c_3021]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_3059,plain,
% 55.37/7.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top
% 55.37/7.50      | r1_xboole_0(k1_xboole_0,X1) != iProver_top ),
% 55.37/7.50      inference(light_normalisation,[status(thm)],[c_3056,c_1770]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_12,plain,
% 55.37/7.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 55.37/7.50      inference(cnf_transformation,[],[f42]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_302,plain,
% 55.37/7.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 55.37/7.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_1,plain,
% 55.37/7.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 55.37/7.50      inference(cnf_transformation,[],[f30]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_306,plain,
% 55.37/7.50      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 55.37/7.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_4919,plain,
% 55.37/7.50      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_302,c_306]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_63686,plain,
% 55.37/7.50      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 55.37/7.50      inference(forward_subsumption_resolution,[status(thm)],[c_3059,c_4919]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_63718,plain,
% 55.37/7.50      ( r1_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X0)))) = iProver_top ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_2590,c_63686]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_158219,plain,
% 55.37/7.50      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k4_xboole_0(X1,k4_xboole_0(X1,sK3))) = iProver_top ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_153984,c_63718]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_14,negated_conjecture,
% 55.37/7.50      ( ~ r1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) ),
% 55.37/7.50      inference(cnf_transformation,[],[f56]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_300,plain,
% 55.37/7.50      ( r1_xboole_0(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)),k4_xboole_0(sK4,k4_xboole_0(sK4,sK3))) != iProver_top ),
% 55.37/7.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.37/7.50  
% 55.37/7.50  cnf(c_254160,plain,
% 55.37/7.50      ( $false ),
% 55.37/7.50      inference(superposition,[status(thm)],[c_158219,c_300]) ).
% 55.37/7.50  
% 55.37/7.50  
% 55.37/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.37/7.50  
% 55.37/7.50  ------                               Statistics
% 55.37/7.50  
% 55.37/7.50  ------ General
% 55.37/7.50  
% 55.37/7.50  abstr_ref_over_cycles:                  0
% 55.37/7.50  abstr_ref_under_cycles:                 0
% 55.37/7.50  gc_basic_clause_elim:                   0
% 55.37/7.50  forced_gc_time:                         0
% 55.37/7.50  parsing_time:                           0.013
% 55.37/7.50  unif_index_cands_time:                  0.
% 55.37/7.50  unif_index_add_time:                    0.
% 55.37/7.50  orderings_time:                         0.
% 55.37/7.50  out_proof_time:                         0.007
% 55.37/7.50  total_time:                             6.884
% 55.37/7.50  num_of_symbols:                         41
% 55.37/7.50  num_of_terms:                           374526
% 55.37/7.50  
% 55.37/7.50  ------ Preprocessing
% 55.37/7.50  
% 55.37/7.50  num_of_splits:                          0
% 55.37/7.50  num_of_split_atoms:                     0
% 55.37/7.50  num_of_reused_defs:                     0
% 55.37/7.50  num_eq_ax_congr_red:                    6
% 55.37/7.50  num_of_sem_filtered_clauses:            1
% 55.37/7.50  num_of_subtypes:                        0
% 55.37/7.50  monotx_restored_types:                  0
% 55.37/7.50  sat_num_of_epr_types:                   0
% 55.37/7.50  sat_num_of_non_cyclic_types:            0
% 55.37/7.50  sat_guarded_non_collapsed_types:        0
% 55.37/7.50  num_pure_diseq_elim:                    0
% 55.37/7.50  simp_replaced_by:                       0
% 55.37/7.50  res_preprocessed:                       61
% 55.37/7.50  prep_upred:                             0
% 55.37/7.50  prep_unflattend:                        3
% 55.37/7.50  smt_new_axioms:                         0
% 55.37/7.50  pred_elim_cands:                        2
% 55.37/7.50  pred_elim:                              0
% 55.37/7.50  pred_elim_cl:                           0
% 55.37/7.50  pred_elim_cycles:                       1
% 55.37/7.50  merged_defs:                            0
% 55.37/7.50  merged_defs_ncl:                        0
% 55.37/7.50  bin_hyper_res:                          0
% 55.37/7.50  prep_cycles:                            3
% 55.37/7.50  pred_elim_time:                         0.001
% 55.37/7.50  splitting_time:                         0.
% 55.37/7.50  sem_filter_time:                        0.
% 55.37/7.50  monotx_time:                            0.001
% 55.37/7.50  subtype_inf_time:                       0.
% 55.37/7.50  
% 55.37/7.50  ------ Problem properties
% 55.37/7.50  
% 55.37/7.50  clauses:                                16
% 55.37/7.50  conjectures:                            2
% 55.37/7.50  epr:                                    3
% 55.37/7.50  horn:                                   14
% 55.37/7.50  ground:                                 2
% 55.37/7.50  unary:                                  11
% 55.37/7.50  binary:                                 5
% 55.37/7.50  lits:                                   21
% 55.37/7.50  lits_eq:                                9
% 55.37/7.50  fd_pure:                                0
% 55.37/7.50  fd_pseudo:                              0
% 55.37/7.50  fd_cond:                                1
% 55.37/7.50  fd_pseudo_cond:                         0
% 55.37/7.50  ac_symbols:                             0
% 55.37/7.50  
% 55.37/7.50  ------ Propositional Solver
% 55.37/7.50  
% 55.37/7.50  prop_solver_calls:                      46
% 55.37/7.50  prop_fast_solver_calls:                 630
% 55.37/7.50  smt_solver_calls:                       0
% 55.37/7.50  smt_fast_solver_calls:                  0
% 55.37/7.50  prop_num_of_clauses:                    45990
% 55.37/7.50  prop_preprocess_simplified:             30388
% 55.37/7.50  prop_fo_subsumed:                       0
% 55.37/7.50  prop_solver_time:                       0.
% 55.37/7.50  smt_solver_time:                        0.
% 55.37/7.50  smt_fast_solver_time:                   0.
% 55.37/7.50  prop_fast_solver_time:                  0.
% 55.37/7.50  prop_unsat_core_time:                   0.
% 55.37/7.50  
% 55.37/7.50  ------ QBF
% 55.37/7.50  
% 55.37/7.50  qbf_q_res:                              0
% 55.37/7.50  qbf_num_tautologies:                    0
% 55.37/7.50  qbf_prep_cycles:                        0
% 55.37/7.50  
% 55.37/7.50  ------ BMC1
% 55.37/7.50  
% 55.37/7.50  bmc1_current_bound:                     -1
% 55.37/7.50  bmc1_last_solved_bound:                 -1
% 55.37/7.50  bmc1_unsat_core_size:                   -1
% 55.37/7.50  bmc1_unsat_core_parents_size:           -1
% 55.37/7.50  bmc1_merge_next_fun:                    0
% 55.37/7.50  bmc1_unsat_core_clauses_time:           0.
% 55.37/7.50  
% 55.37/7.50  ------ Instantiation
% 55.37/7.50  
% 55.37/7.50  inst_num_of_clauses:                    5215
% 55.37/7.50  inst_num_in_passive:                    1647
% 55.37/7.50  inst_num_in_active:                     1517
% 55.37/7.50  inst_num_in_unprocessed:                2051
% 55.37/7.50  inst_num_of_loops:                      1580
% 55.37/7.50  inst_num_of_learning_restarts:          0
% 55.37/7.50  inst_num_moves_active_passive:          61
% 55.37/7.50  inst_lit_activity:                      0
% 55.37/7.50  inst_lit_activity_moves:                0
% 55.37/7.50  inst_num_tautologies:                   0
% 55.37/7.50  inst_num_prop_implied:                  0
% 55.37/7.50  inst_num_existing_simplified:           0
% 55.37/7.50  inst_num_eq_res_simplified:             0
% 55.37/7.50  inst_num_child_elim:                    0
% 55.37/7.50  inst_num_of_dismatching_blockings:      1868
% 55.37/7.50  inst_num_of_non_proper_insts:           4762
% 55.37/7.50  inst_num_of_duplicates:                 0
% 55.37/7.50  inst_inst_num_from_inst_to_res:         0
% 55.37/7.50  inst_dismatching_checking_time:         0.
% 55.37/7.50  
% 55.37/7.50  ------ Resolution
% 55.37/7.50  
% 55.37/7.50  res_num_of_clauses:                     0
% 55.37/7.50  res_num_in_passive:                     0
% 55.37/7.50  res_num_in_active:                      0
% 55.37/7.50  res_num_of_loops:                       64
% 55.37/7.50  res_forward_subset_subsumed:            172
% 55.37/7.50  res_backward_subset_subsumed:           0
% 55.37/7.50  res_forward_subsumed:                   0
% 55.37/7.50  res_backward_subsumed:                  0
% 55.37/7.50  res_forward_subsumption_resolution:     0
% 55.37/7.50  res_backward_subsumption_resolution:    0
% 55.37/7.50  res_clause_to_clause_subsumption:       907082
% 55.37/7.50  res_orphan_elimination:                 0
% 55.37/7.50  res_tautology_del:                      120
% 55.37/7.50  res_num_eq_res_simplified:              0
% 55.37/7.50  res_num_sel_changes:                    0
% 55.37/7.50  res_moves_from_active_to_pass:          0
% 55.37/7.50  
% 55.37/7.50  ------ Superposition
% 55.37/7.50  
% 55.37/7.50  sup_time_total:                         0.
% 55.37/7.50  sup_time_generating:                    0.
% 55.37/7.50  sup_time_sim_full:                      0.
% 55.37/7.50  sup_time_sim_immed:                     0.
% 55.37/7.50  
% 55.37/7.50  sup_num_of_clauses:                     15257
% 55.37/7.50  sup_num_in_active:                      294
% 55.37/7.50  sup_num_in_passive:                     14963
% 55.37/7.50  sup_num_of_loops:                       315
% 55.37/7.50  sup_fw_superposition:                   50482
% 55.37/7.50  sup_bw_superposition:                   45543
% 55.37/7.50  sup_immediate_simplified:               44214
% 55.37/7.50  sup_given_eliminated:                   9
% 55.37/7.50  comparisons_done:                       0
% 55.37/7.50  comparisons_avoided:                    0
% 55.37/7.50  
% 55.37/7.50  ------ Simplifications
% 55.37/7.50  
% 55.37/7.50  
% 55.37/7.50  sim_fw_subset_subsumed:                 88
% 55.37/7.50  sim_bw_subset_subsumed:                 35
% 55.37/7.50  sim_fw_subsumed:                        9510
% 55.37/7.50  sim_bw_subsumed:                        206
% 55.37/7.50  sim_fw_subsumption_res:                 2
% 55.37/7.50  sim_bw_subsumption_res:                 0
% 55.37/7.50  sim_tautology_del:                      69
% 55.37/7.50  sim_eq_tautology_del:                   6871
% 55.37/7.50  sim_eq_res_simp:                        0
% 55.37/7.50  sim_fw_demodulated:                     36513
% 55.37/7.50  sim_bw_demodulated:                     899
% 55.37/7.50  sim_light_normalised:                   12774
% 55.37/7.50  sim_joinable_taut:                      0
% 55.37/7.50  sim_joinable_simp:                      0
% 55.37/7.50  sim_ac_normalised:                      0
% 55.37/7.50  sim_smt_subsumption:                    0
% 55.37/7.50  
%------------------------------------------------------------------------------
