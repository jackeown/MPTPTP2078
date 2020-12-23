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
% DateTime   : Thu Dec  3 11:25:42 EST 2020

% Result     : Theorem 54.78s
% Output     : CNFRefutation 54.78s
% Verified   : 
% Statistics : Number of formulae       :  200 (12251 expanded)
%              Number of clauses        :  150 (4556 expanded)
%              Number of leaves         :   20 (3066 expanded)
%              Depth                    :   48
%              Number of atoms          :  301 (15387 expanded)
%              Number of equality atoms :  203 (11231 expanded)
%              Maximal formula depth    :    8 (   2 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f24])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f42,f36,f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK1,sK3)
        | ~ r1_tarski(sK1,sK2) )
      & r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( ~ r1_xboole_0(sK1,sK3)
      | ~ r1_tarski(sK1,sK2) )
    & r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f27])).

fof(f47,plain,(
    r1_tarski(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(definition_unfolding,[],[f47,f36])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f36])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f48,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_222269,plain,
    ( ~ r2_hidden(k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)),k3_xboole_0(sK3,sK1))
    | ~ r1_xboole_0(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_218455,plain,
    ( k3_xboole_0(sK3,sK1) = k3_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_369,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_215297,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK1,sK3),k3_xboole_0(sK1,sK3))
    | X0 != sK0(sK1,sK3)
    | X1 != k3_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_216413,plain,
    ( ~ r2_hidden(sK0(sK1,sK3),k3_xboole_0(sK1,sK3))
    | r2_hidden(k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)),X0)
    | X0 != k3_xboole_0(sK1,sK3)
    | k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)) != sK0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_215297])).

cnf(c_218454,plain,
    ( ~ r2_hidden(sK0(sK1,sK3),k3_xboole_0(sK1,sK3))
    | r2_hidden(k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)),k3_xboole_0(sK3,sK1))
    | k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)) != sK0(sK1,sK3)
    | k3_xboole_0(sK3,sK1) != k3_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_216413])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_734,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1260,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_734])).

cnf(c_12,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1117,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_12])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_736,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11558,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1260,c_736])).

cnf(c_11698,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11558,c_2])).

cnf(c_18913,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1117,c_11698])).

cnf(c_18921,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_18913])).

cnf(c_11,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1121,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0)))) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_12,c_11])).

cnf(c_24432,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18921,c_1121])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_24557,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_24432,c_8])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_25242,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_24557,c_0])).

cnf(c_29984,plain,
    ( k2_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1),k1_xboole_0) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_18921,c_25242])).

cnf(c_30012,plain,
    ( k2_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_29984,c_8,c_18921])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_733,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2035,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_734,c_733])).

cnf(c_45153,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2035,c_1])).

cnf(c_59260,plain,
    ( k2_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_30012,c_45153])).

cnf(c_59346,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_59260,c_8])).

cnf(c_59454,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_59346])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_726,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1014,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1,c_726])).

cnf(c_2037,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_1014,c_733])).

cnf(c_2593,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2037,c_12])).

cnf(c_60442,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[status(thm)],[c_59454,c_2593])).

cnf(c_10,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_732,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1621,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_732])).

cnf(c_2378,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1621])).

cnf(c_9172,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_2378])).

cnf(c_13648,plain,
    ( r1_tarski(sK1,k3_xboole_0(sK2,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2037,c_9172])).

cnf(c_13767,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_13648,c_733])).

cnf(c_1120,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_12])).

cnf(c_2059,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_1120])).

cnf(c_14018,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k3_xboole_0(sK2,sK1),sK1)) = k3_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK2,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_13767,c_2059])).

cnf(c_14062,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK2,sK1),sK1)) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_14018,c_2,c_12,c_11698])).

cnf(c_1115,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_1,c_12])).

cnf(c_16985,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) = k5_xboole_0(k3_xboole_0(sK2,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_13767,c_1115])).

cnf(c_17047,plain,
    ( k5_xboole_0(k3_xboole_0(sK2,sK1),sK1) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_16985,c_2,c_11698])).

cnf(c_30737,plain,
    ( k3_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK2,k1_xboole_0)) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_14062,c_17047])).

cnf(c_30741,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK2,k1_xboole_0)) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_30737])).

cnf(c_34410,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,sK2)) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_30741])).

cnf(c_37645,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_34410,c_1])).

cnf(c_2056,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_12,c_1120])).

cnf(c_2107,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_2056,c_12])).

cnf(c_88280,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK2,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[status(thm)],[c_37645,c_2107])).

cnf(c_88622,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK2,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK2,k1_xboole_0))) ),
    inference(light_normalisation,[status(thm)],[c_88280,c_37645])).

cnf(c_45066,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_2035])).

cnf(c_46176,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_45066,c_12])).

cnf(c_46333,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_46176,c_2,c_11698])).

cnf(c_88623,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_88622,c_46333])).

cnf(c_88624,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_88623,c_2])).

cnf(c_89366,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_88624])).

cnf(c_90478,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_89366,c_1])).

cnf(c_113834,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,sK2))))) ),
    inference(superposition,[status(thm)],[c_90478,c_2107])).

cnf(c_113889,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_113834,c_90478])).

cnf(c_113891,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_113889,c_46333])).

cnf(c_113892,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_113891,c_2])).

cnf(c_123163,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_113892])).

cnf(c_124745,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_123163,c_123163])).

cnf(c_1258,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_734])).

cnf(c_2038,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1258,c_733])).

cnf(c_51899,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2038,c_1])).

cnf(c_1624,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_732])).

cnf(c_2040,plain,
    ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1624,c_733])).

cnf(c_53716,plain,
    ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_51899,c_2040])).

cnf(c_54194,plain,
    ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_53716,c_2,c_1115,c_11698])).

cnf(c_124756,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_124745,c_2,c_54194])).

cnf(c_129326,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0))) = k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_124756,c_12])).

cnf(c_937,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_0])).

cnf(c_1101,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_11,c_937])).

cnf(c_1103,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1101,c_937])).

cnf(c_129351,plain,
    ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[status(thm)],[c_124756,c_1103])).

cnf(c_129406,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_129326,c_129351])).

cnf(c_1118,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_1,c_12])).

cnf(c_129408,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(demodulation,[status(thm)],[c_129406,c_1118])).

cnf(c_2068,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) ),
    inference(superposition,[status(thm)],[c_1120,c_12])).

cnf(c_64788,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X0)) = k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X0)))) ),
    inference(superposition,[status(thm)],[c_2040,c_2068])).

cnf(c_1403,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_1103])).

cnf(c_65644,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_64788,c_2,c_1403,c_11698])).

cnf(c_129409,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,k1_xboole_0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(demodulation,[status(thm)],[c_129408,c_65644])).

cnf(c_129410,plain,
    ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_129409,c_2])).

cnf(c_89350,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_88624])).

cnf(c_89997,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1,c_89350])).

cnf(c_109348,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_89997,c_1])).

cnf(c_135878,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_129410,c_109348])).

cnf(c_147400,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_135878,c_2038,c_54194])).

cnf(c_147401,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_147400,c_2,c_54194])).

cnf(c_155274,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_147401,c_2107])).

cnf(c_155305,plain,
    ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_147401,c_89350])).

cnf(c_155664,plain,
    ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_155305,c_2035])).

cnf(c_155769,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) ),
    inference(demodulation,[status(thm)],[c_155274,c_155664])).

cnf(c_155771,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_155769,c_2,c_1103])).

cnf(c_209231,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) ),
    inference(superposition,[status(thm)],[c_60442,c_155771])).

cnf(c_209647,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_209231,c_2037])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_728,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1905,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(X0,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_728])).

cnf(c_210727,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_xboole_0(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_209647,c_1905])).

cnf(c_211613,plain,
    ( r1_xboole_0(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_210727])).

cnf(c_211637,plain,
    ( r1_xboole_0(sK3,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_211613])).

cnf(c_3102,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),X1))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_2593,c_12])).

cnf(c_182369,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1103,c_3102])).

cnf(c_16990,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_2037,c_1115])).

cnf(c_183134,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_182369,c_16990])).

cnf(c_186509,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k5_xboole_0(sK1,sK1),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK2,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_13767,c_183134])).

cnf(c_186673,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_186509,c_1103,c_2038,c_11698])).

cnf(c_125223,plain,
    ( k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)) = sK0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_365,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1203,plain,
    ( k5_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k5_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_91771,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1203])).

cnf(c_91772,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) != k1_xboole_0
    | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_91771])).

cnf(c_999,plain,
    ( X0 != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) = X0 ),
    inference(instantiation,[status(thm)],[c_365])).

cnf(c_1219,plain,
    ( X0 != k5_xboole_0(X1,X2)
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) = X0
    | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != k5_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_999])).

cnf(c_2554,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k5_xboole_0(X0,X1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_29869,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_2554])).

cnf(c_370,plain,
    ( X0 != X1
    | X2 != X3
    | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_1001,plain,
    ( X0 != X1
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k5_xboole_0(X1,X3)
    | k3_xboole_0(X0,X2) != X3 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_2850,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,X1)
    | k3_xboole_0(sK1,sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_6124,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k3_xboole_0(sK2,sK1))
    | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_14456,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))
    | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_6124])).

cnf(c_6125,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_364,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_986,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_874,plain,
    ( r2_hidden(sK0(sK1,sK3),k3_xboole_0(sK1,sK3))
    | r1_xboole_0(sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_377,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_119,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_276,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_119,c_17])).

cnf(c_277,plain,
    ( ~ r1_xboole_0(sK1,sK3)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_222269,c_218455,c_218454,c_211637,c_186673,c_125223,c_91772,c_29869,c_14456,c_6125,c_986,c_874,c_377,c_277])).

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
% 0.12/0.34  % DateTime   : Tue Dec  1 12:53:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 54.78/7.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 54.78/7.49  
% 54.78/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 54.78/7.49  
% 54.78/7.49  ------  iProver source info
% 54.78/7.49  
% 54.78/7.49  git: date: 2020-06-30 10:37:57 +0100
% 54.78/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 54.78/7.49  git: non_committed_changes: false
% 54.78/7.49  git: last_make_outside_of_git: false
% 54.78/7.49  
% 54.78/7.49  ------ 
% 54.78/7.49  ------ Parsing...
% 54.78/7.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 54.78/7.49  
% 54.78/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 54.78/7.49  
% 54.78/7.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 54.78/7.49  
% 54.78/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 54.78/7.49  ------ Proving...
% 54.78/7.49  ------ Problem Properties 
% 54.78/7.49  
% 54.78/7.49  
% 54.78/7.49  clauses                                 19
% 54.78/7.49  conjectures                             2
% 54.78/7.49  EPR                                     1
% 54.78/7.49  Horn                                    18
% 54.78/7.49  unary                                   9
% 54.78/7.49  binary                                  9
% 54.78/7.49  lits                                    30
% 54.78/7.49  lits eq                                 9
% 54.78/7.49  fd_pure                                 0
% 54.78/7.49  fd_pseudo                               0
% 54.78/7.49  fd_cond                                 0
% 54.78/7.49  fd_pseudo_cond                          0
% 54.78/7.49  AC symbols                              0
% 54.78/7.49  
% 54.78/7.49  ------ Input Options Time Limit: Unbounded
% 54.78/7.49  
% 54.78/7.49  
% 54.78/7.49  ------ 
% 54.78/7.49  Current options:
% 54.78/7.49  ------ 
% 54.78/7.49  
% 54.78/7.49  
% 54.78/7.49  
% 54.78/7.49  
% 54.78/7.49  ------ Proving...
% 54.78/7.49  
% 54.78/7.49  
% 54.78/7.49  % SZS status Theorem for theBenchmark.p
% 54.78/7.49  
% 54.78/7.49  % SZS output start CNFRefutation for theBenchmark.p
% 54.78/7.49  
% 54.78/7.49  fof(f4,axiom,(
% 54.78/7.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f18,plain,(
% 54.78/7.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 54.78/7.49    inference(rectify,[],[f4])).
% 54.78/7.49  
% 54.78/7.49  fof(f19,plain,(
% 54.78/7.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 54.78/7.49    inference(ennf_transformation,[],[f18])).
% 54.78/7.49  
% 54.78/7.49  fof(f24,plain,(
% 54.78/7.49    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 54.78/7.49    introduced(choice_axiom,[])).
% 54.78/7.49  
% 54.78/7.49  fof(f25,plain,(
% 54.78/7.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 54.78/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f24])).
% 54.78/7.49  
% 54.78/7.49  fof(f33,plain,(
% 54.78/7.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 54.78/7.49    inference(cnf_transformation,[],[f25])).
% 54.78/7.49  
% 54.78/7.49  fof(f2,axiom,(
% 54.78/7.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f30,plain,(
% 54.78/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 54.78/7.49    inference(cnf_transformation,[],[f2])).
% 54.78/7.49  
% 54.78/7.49  fof(f3,axiom,(
% 54.78/7.49    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f17,plain,(
% 54.78/7.49    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 54.78/7.49    inference(rectify,[],[f3])).
% 54.78/7.49  
% 54.78/7.49  fof(f31,plain,(
% 54.78/7.49    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 54.78/7.49    inference(cnf_transformation,[],[f17])).
% 54.78/7.49  
% 54.78/7.49  fof(f7,axiom,(
% 54.78/7.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f37,plain,(
% 54.78/7.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 54.78/7.49    inference(cnf_transformation,[],[f7])).
% 54.78/7.49  
% 54.78/7.49  fof(f12,axiom,(
% 54.78/7.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f42,plain,(
% 54.78/7.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 54.78/7.49    inference(cnf_transformation,[],[f12])).
% 54.78/7.49  
% 54.78/7.49  fof(f6,axiom,(
% 54.78/7.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f36,plain,(
% 54.78/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 54.78/7.49    inference(cnf_transformation,[],[f6])).
% 54.78/7.49  
% 54.78/7.49  fof(f53,plain,(
% 54.78/7.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 54.78/7.49    inference(definition_unfolding,[],[f42,f36,f36])).
% 54.78/7.49  
% 54.78/7.49  fof(f5,axiom,(
% 54.78/7.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f26,plain,(
% 54.78/7.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 54.78/7.49    inference(nnf_transformation,[],[f5])).
% 54.78/7.49  
% 54.78/7.49  fof(f35,plain,(
% 54.78/7.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 54.78/7.49    inference(cnf_transformation,[],[f26])).
% 54.78/7.49  
% 54.78/7.49  fof(f49,plain,(
% 54.78/7.49    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 54.78/7.49    inference(definition_unfolding,[],[f35,f36])).
% 54.78/7.49  
% 54.78/7.49  fof(f11,axiom,(
% 54.78/7.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f41,plain,(
% 54.78/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 54.78/7.49    inference(cnf_transformation,[],[f11])).
% 54.78/7.49  
% 54.78/7.49  fof(f52,plain,(
% 54.78/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 54.78/7.49    inference(definition_unfolding,[],[f41,f36])).
% 54.78/7.49  
% 54.78/7.49  fof(f8,axiom,(
% 54.78/7.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f38,plain,(
% 54.78/7.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 54.78/7.49    inference(cnf_transformation,[],[f8])).
% 54.78/7.49  
% 54.78/7.49  fof(f1,axiom,(
% 54.78/7.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f29,plain,(
% 54.78/7.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 54.78/7.49    inference(cnf_transformation,[],[f1])).
% 54.78/7.49  
% 54.78/7.49  fof(f9,axiom,(
% 54.78/7.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f20,plain,(
% 54.78/7.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 54.78/7.49    inference(ennf_transformation,[],[f9])).
% 54.78/7.49  
% 54.78/7.49  fof(f39,plain,(
% 54.78/7.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 54.78/7.49    inference(cnf_transformation,[],[f20])).
% 54.78/7.49  
% 54.78/7.49  fof(f15,conjecture,(
% 54.78/7.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f16,negated_conjecture,(
% 54.78/7.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 54.78/7.49    inference(negated_conjecture,[],[f15])).
% 54.78/7.49  
% 54.78/7.49  fof(f23,plain,(
% 54.78/7.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 54.78/7.49    inference(ennf_transformation,[],[f16])).
% 54.78/7.49  
% 54.78/7.49  fof(f27,plain,(
% 54.78/7.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)) & r1_tarski(sK1,k4_xboole_0(sK2,sK3)))),
% 54.78/7.49    introduced(choice_axiom,[])).
% 54.78/7.49  
% 54.78/7.49  fof(f28,plain,(
% 54.78/7.49    (~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)) & r1_tarski(sK1,k4_xboole_0(sK2,sK3))),
% 54.78/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f23,f27])).
% 54.78/7.49  
% 54.78/7.49  fof(f47,plain,(
% 54.78/7.49    r1_tarski(sK1,k4_xboole_0(sK2,sK3))),
% 54.78/7.49    inference(cnf_transformation,[],[f28])).
% 54.78/7.49  
% 54.78/7.49  fof(f55,plain,(
% 54.78/7.49    r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)))),
% 54.78/7.49    inference(definition_unfolding,[],[f47,f36])).
% 54.78/7.49  
% 54.78/7.49  fof(f10,axiom,(
% 54.78/7.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f40,plain,(
% 54.78/7.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 54.78/7.49    inference(cnf_transformation,[],[f10])).
% 54.78/7.49  
% 54.78/7.49  fof(f51,plain,(
% 54.78/7.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 54.78/7.49    inference(definition_unfolding,[],[f40,f36])).
% 54.78/7.49  
% 54.78/7.49  fof(f14,axiom,(
% 54.78/7.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 54.78/7.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 54.78/7.49  
% 54.78/7.49  fof(f22,plain,(
% 54.78/7.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 54.78/7.49    inference(ennf_transformation,[],[f14])).
% 54.78/7.49  
% 54.78/7.49  fof(f46,plain,(
% 54.78/7.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 54.78/7.49    inference(cnf_transformation,[],[f22])).
% 54.78/7.49  
% 54.78/7.49  fof(f54,plain,(
% 54.78/7.49    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 54.78/7.49    inference(definition_unfolding,[],[f46,f36])).
% 54.78/7.49  
% 54.78/7.49  fof(f32,plain,(
% 54.78/7.49    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 54.78/7.49    inference(cnf_transformation,[],[f25])).
% 54.78/7.49  
% 54.78/7.49  fof(f34,plain,(
% 54.78/7.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 54.78/7.49    inference(cnf_transformation,[],[f26])).
% 54.78/7.49  
% 54.78/7.49  fof(f50,plain,(
% 54.78/7.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 54.78/7.49    inference(definition_unfolding,[],[f34,f36])).
% 54.78/7.49  
% 54.78/7.49  fof(f48,plain,(
% 54.78/7.49    ~r1_xboole_0(sK1,sK3) | ~r1_tarski(sK1,sK2)),
% 54.78/7.49    inference(cnf_transformation,[],[f28])).
% 54.78/7.49  
% 54.78/7.49  cnf(c_3,plain,
% 54.78/7.49      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 54.78/7.49      inference(cnf_transformation,[],[f33]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_222269,plain,
% 54.78/7.49      ( ~ r2_hidden(k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)),k3_xboole_0(sK3,sK1))
% 54.78/7.49      | ~ r1_xboole_0(sK3,sK1) ),
% 54.78/7.49      inference(instantiation,[status(thm)],[c_3]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1,plain,
% 54.78/7.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 54.78/7.49      inference(cnf_transformation,[],[f30]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_218455,plain,
% 54.78/7.49      ( k3_xboole_0(sK3,sK1) = k3_xboole_0(sK1,sK3) ),
% 54.78/7.49      inference(instantiation,[status(thm)],[c_1]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_369,plain,
% 54.78/7.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 54.78/7.49      theory(equality) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_215297,plain,
% 54.78/7.49      ( r2_hidden(X0,X1)
% 54.78/7.49      | ~ r2_hidden(sK0(sK1,sK3),k3_xboole_0(sK1,sK3))
% 54.78/7.49      | X0 != sK0(sK1,sK3)
% 54.78/7.49      | X1 != k3_xboole_0(sK1,sK3) ),
% 54.78/7.49      inference(instantiation,[status(thm)],[c_369]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_216413,plain,
% 54.78/7.49      ( ~ r2_hidden(sK0(sK1,sK3),k3_xboole_0(sK1,sK3))
% 54.78/7.49      | r2_hidden(k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)),X0)
% 54.78/7.49      | X0 != k3_xboole_0(sK1,sK3)
% 54.78/7.49      | k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)) != sK0(sK1,sK3) ),
% 54.78/7.49      inference(instantiation,[status(thm)],[c_215297]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_218454,plain,
% 54.78/7.49      ( ~ r2_hidden(sK0(sK1,sK3),k3_xboole_0(sK1,sK3))
% 54.78/7.49      | r2_hidden(k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)),k3_xboole_0(sK3,sK1))
% 54.78/7.49      | k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)) != sK0(sK1,sK3)
% 54.78/7.49      | k3_xboole_0(sK3,sK1) != k3_xboole_0(sK1,sK3) ),
% 54.78/7.49      inference(instantiation,[status(thm)],[c_216413]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2,plain,
% 54.78/7.49      ( k3_xboole_0(X0,X0) = X0 ),
% 54.78/7.49      inference(cnf_transformation,[],[f31]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_7,plain,
% 54.78/7.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 54.78/7.49      inference(cnf_transformation,[],[f37]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_734,plain,
% 54.78/7.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 54.78/7.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1260,plain,
% 54.78/7.49      ( r1_tarski(X0,X0) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_2,c_734]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_12,plain,
% 54.78/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 54.78/7.49      inference(cnf_transformation,[],[f53]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1117,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_2,c_12]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_5,plain,
% 54.78/7.49      ( ~ r1_tarski(X0,X1)
% 54.78/7.49      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 54.78/7.49      inference(cnf_transformation,[],[f49]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_736,plain,
% 54.78/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 54.78/7.49      | r1_tarski(X0,X1) != iProver_top ),
% 54.78/7.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_11558,plain,
% 54.78/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1260,c_736]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_11698,plain,
% 54.78/7.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 54.78/7.49      inference(light_normalisation,[status(thm)],[c_11558,c_2]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_18913,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) = k1_xboole_0 ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_1117,c_11698]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_18921,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X0)))) = k1_xboole_0 ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_18913]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_11,plain,
% 54.78/7.49      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 54.78/7.49      inference(cnf_transformation,[],[f52]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1121,plain,
% 54.78/7.49      ( k2_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0)))) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_12,c_11]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_24432,plain,
% 54.78/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k2_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_18921,c_1121]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_8,plain,
% 54.78/7.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 54.78/7.49      inference(cnf_transformation,[],[f38]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_24557,plain,
% 54.78/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_24432,c_8]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_0,plain,
% 54.78/7.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 54.78/7.49      inference(cnf_transformation,[],[f29]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_25242,plain,
% 54.78/7.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_24557,c_0]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_29984,plain,
% 54.78/7.49      ( k2_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1),k1_xboole_0) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_18921,c_25242]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_30012,plain,
% 54.78/7.49      ( k2_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))),X1),k1_xboole_0) = k1_xboole_0 ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_29984,c_8,c_18921]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_9,plain,
% 54.78/7.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 54.78/7.49      inference(cnf_transformation,[],[f39]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_733,plain,
% 54.78/7.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 54.78/7.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2035,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_734,c_733]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_45153,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_2035,c_1]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_59260,plain,
% 54.78/7.49      ( k2_xboole_0(k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1),k1_xboole_0) = k1_xboole_0 ),
% 54.78/7.49      inference(light_normalisation,[status(thm)],[c_30012,c_45153]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_59346,plain,
% 54.78/7.49      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_59260,c_8]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_59454,plain,
% 54.78/7.49      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = k1_xboole_0 ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_59346]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_18,negated_conjecture,
% 54.78/7.49      ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) ),
% 54.78/7.49      inference(cnf_transformation,[],[f55]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_726,plain,
% 54.78/7.49      ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK3))) = iProver_top ),
% 54.78/7.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1014,plain,
% 54.78/7.49      ( r1_tarski(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = iProver_top ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_1,c_726]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2037,plain,
% 54.78/7.49      ( k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) = sK1 ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1014,c_733]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2593,plain,
% 54.78/7.49      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_2037,c_12]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_60442,plain,
% 54.78/7.49      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_59454,c_2593]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_10,plain,
% 54.78/7.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 54.78/7.49      inference(cnf_transformation,[],[f51]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_732,plain,
% 54.78/7.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 54.78/7.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1621,plain,
% 54.78/7.49      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(X0,X1)) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_12,c_732]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2378,plain,
% 54.78/7.49      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X0,X1)) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_1621]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_9172,plain,
% 54.78/7.49      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))),k3_xboole_0(X1,X0)) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_2378]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_13648,plain,
% 54.78/7.49      ( r1_tarski(sK1,k3_xboole_0(sK2,sK1)) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_2037,c_9172]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_13767,plain,
% 54.78/7.49      ( k3_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = sK1 ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_13648,c_733]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1120,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_2,c_12]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2059,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_1120]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_14018,plain,
% 54.78/7.49      ( k5_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(k3_xboole_0(sK2,sK1),sK1)) = k3_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK2,sK1),sK1)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_13767,c_2059]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_14062,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(sK2,sK1),k5_xboole_0(k3_xboole_0(sK2,sK1),sK1)) = k3_xboole_0(sK2,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_14018,c_2,c_12,c_11698]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1115,plain,
% 54.78/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_12]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_16985,plain,
% 54.78/7.49      ( k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))) = k5_xboole_0(k3_xboole_0(sK2,sK1),sK1) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_13767,c_1115]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_17047,plain,
% 54.78/7.49      ( k5_xboole_0(k3_xboole_0(sK2,sK1),sK1) = k3_xboole_0(sK2,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_16985,c_2,c_11698]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_30737,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(sK2,sK1),k3_xboole_0(sK2,k1_xboole_0)) = k3_xboole_0(sK2,k1_xboole_0) ),
% 54.78/7.49      inference(light_normalisation,[status(thm)],[c_14062,c_17047]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_30741,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK2,k1_xboole_0)) = k3_xboole_0(sK2,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_30737]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_34410,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k1_xboole_0,sK2)) = k3_xboole_0(sK2,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_30741]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_37645,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK2,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_34410,c_1]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2056,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_12,c_1120]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2107,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 54.78/7.49      inference(light_normalisation,[status(thm)],[c_2056,c_12]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_88280,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK2,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK1,sK2)))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_37645,c_2107]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_88622,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK2,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(sK2,k1_xboole_0))) ),
% 54.78/7.49      inference(light_normalisation,[status(thm)],[c_88280,c_37645]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_45066,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_2035]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_46176,plain,
% 54.78/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_45066,c_12]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_46333,plain,
% 54.78/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_46176,c_2,c_11698]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_88623,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_88622,c_46333]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_88624,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_88623,c_2]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_89366,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2)),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_88624]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_90478,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,sK2))) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_89366,c_1]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_113834,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,sK2))))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_90478,c_2107]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_113889,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(X1,k1_xboole_0))) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_113834,c_90478]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_113891,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_113889,c_46333]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_113892,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_113891,c_2]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_123163,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_113892]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_124745,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)))) = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_123163,c_123163]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1258,plain,
% 54.78/7.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_734]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2038,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1258,c_733]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_51899,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_2038,c_1]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1624,plain,
% 54.78/7.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_732]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2040,plain,
% 54.78/7.49      ( k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1624,c_733]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_53716,plain,
% 54.78/7.49      ( k3_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,k3_xboole_0(X0,X1))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_51899,c_2040]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_54194,plain,
% 54.78/7.49      ( k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_53716,c_2,c_1115,c_11698]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_124756,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_124745,c_2,c_54194]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_129326,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0))) = k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k1_xboole_0)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_124756,c_12]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_937,plain,
% 54.78/7.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_8,c_0]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1101,plain,
% 54.78/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,X0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_11,c_937]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1103,plain,
% 54.78/7.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 54.78/7.49      inference(light_normalisation,[status(thm)],[c_1101,c_937]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_129351,plain,
% 54.78/7.49      ( k5_xboole_0(k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_124756,c_1103]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_129406,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X1),k3_xboole_0(k3_xboole_0(k1_xboole_0,X1),k1_xboole_0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
% 54.78/7.49      inference(light_normalisation,[status(thm)],[c_129326,c_129351]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1118,plain,
% 54.78/7.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_12]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_129408,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_129406,c_1118]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_2068,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2))) = k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1120,c_12]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_64788,plain,
% 54.78/7.49      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),X0)) = k3_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k5_xboole_0(X0,k3_xboole_0(X0,X0)))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_2040,c_2068]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1403,plain,
% 54.78/7.49      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_2,c_1103]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_65644,plain,
% 54.78/7.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(light_normalisation,
% 54.78/7.49                [status(thm)],
% 54.78/7.49                [c_64788,c_2,c_1403,c_11698]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_129409,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(k1_xboole_0,k1_xboole_0))) = k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_129408,c_65644]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_129410,plain,
% 54.78/7.49      ( k3_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k3_xboole_0(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_129409,c_2]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_89350,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0),k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_88624]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_89997,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0),k3_xboole_0(k1_xboole_0,X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1,c_89350]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_109348,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,X0),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_89997,c_1]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_135878,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_129410,c_109348]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_147400,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k3_xboole_0(X0,k1_xboole_0))) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_135878,c_2038,c_54194]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_147401,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_147400,c_2,c_54194]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_155274,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_147401,c_2107]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_155305,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0),k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),k1_xboole_0)) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_147401,c_89350]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_155664,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_155305,c_2035]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_155769,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k1_xboole_0,k1_xboole_0)))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_155274,c_155664]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_155771,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,k1_xboole_0))) = k3_xboole_0(X0,X1) ),
% 54.78/7.49      inference(demodulation,[status(thm)],[c_155769,c_2,c_1103]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_209231,plain,
% 54.78/7.49      ( k3_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))),k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = k3_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK3,sK2))) ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_60442,c_155771]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_209647,plain,
% 54.78/7.49      ( k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK3))) = sK1 ),
% 54.78/7.49      inference(light_normalisation,[status(thm)],[c_209231,c_2037]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_16,plain,
% 54.78/7.49      ( ~ r1_tarski(X0,X1)
% 54.78/7.49      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 54.78/7.49      inference(cnf_transformation,[],[f54]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_728,plain,
% 54.78/7.49      ( r1_tarski(X0,X1) != iProver_top
% 54.78/7.49      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = iProver_top ),
% 54.78/7.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_1905,plain,
% 54.78/7.49      ( r1_tarski(X0,X1) != iProver_top
% 54.78/7.49      | r1_xboole_0(X0,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X1)))) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_12,c_728]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_210727,plain,
% 54.78/7.49      ( r1_tarski(X0,sK3) != iProver_top
% 54.78/7.49      | r1_xboole_0(X0,sK1) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_209647,c_1905]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_211613,plain,
% 54.78/7.49      ( r1_xboole_0(sK3,sK1) = iProver_top ),
% 54.78/7.49      inference(superposition,[status(thm)],[c_1260,c_210727]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_211637,plain,
% 54.78/7.49      ( r1_xboole_0(sK3,sK1) ),
% 54.78/7.49      inference(predicate_to_equality_rev,[status(thm)],[c_211613]) ).
% 54.78/7.49  
% 54.78/7.49  cnf(c_3102,plain,
% 54.78/7.49      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),k3_xboole_0(k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0)),X1))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),X1)) ),
% 54.78/7.50      inference(superposition,[status(thm)],[c_2593,c_12]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_182369,plain,
% 54.78/7.50      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_xboole_0)) ),
% 54.78/7.50      inference(superposition,[status(thm)],[c_1103,c_3102]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_16990,plain,
% 54.78/7.50      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),k3_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)),X0))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
% 54.78/7.50      inference(superposition,[status(thm)],[c_2037,c_1115]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_183134,plain,
% 54.78/7.50      ( k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,X0)),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
% 54.78/7.50      inference(light_normalisation,[status(thm)],[c_182369,c_16990]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_186509,plain,
% 54.78/7.50      ( k5_xboole_0(k5_xboole_0(sK1,sK1),k3_xboole_0(k5_xboole_0(sK1,sK1),k1_xboole_0)) = k5_xboole_0(sK1,k3_xboole_0(k3_xboole_0(sK2,sK1),sK1)) ),
% 54.78/7.50      inference(superposition,[status(thm)],[c_13767,c_183134]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_186673,plain,
% 54.78/7.50      ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 54.78/7.50      inference(demodulation,
% 54.78/7.50                [status(thm)],
% 54.78/7.50                [c_186509,c_1103,c_2038,c_11698]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_125223,plain,
% 54.78/7.50      ( k3_xboole_0(sK0(sK1,sK3),sK0(sK1,sK3)) = sK0(sK1,sK3) ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_2]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_365,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_1203,plain,
% 54.78/7.50      ( k5_xboole_0(X0,X1) != X2
% 54.78/7.50      | k1_xboole_0 != X2
% 54.78/7.50      | k1_xboole_0 = k5_xboole_0(X0,X1) ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_365]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_91771,plain,
% 54.78/7.50      ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) != X0
% 54.78/7.50      | k1_xboole_0 != X0
% 54.78/7.50      | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_1203]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_91772,plain,
% 54.78/7.50      ( k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) != k1_xboole_0
% 54.78/7.50      | k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))
% 54.78/7.50      | k1_xboole_0 != k1_xboole_0 ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_91771]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_999,plain,
% 54.78/7.50      ( X0 != X1
% 54.78/7.50      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X1
% 54.78/7.50      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) = X0 ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_365]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_1219,plain,
% 54.78/7.50      ( X0 != k5_xboole_0(X1,X2)
% 54.78/7.50      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) = X0
% 54.78/7.50      | k5_xboole_0(X3,k3_xboole_0(X3,X4)) != k5_xboole_0(X1,X2) ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_999]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_2554,plain,
% 54.78/7.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k5_xboole_0(X0,X1)
% 54.78/7.50      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k1_xboole_0
% 54.78/7.50      | k1_xboole_0 != k5_xboole_0(X0,X1) ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_1219]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_29869,plain,
% 54.78/7.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))
% 54.78/7.50      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k1_xboole_0
% 54.78/7.50      | k1_xboole_0 != k5_xboole_0(sK1,k3_xboole_0(sK2,sK1)) ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_2554]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_370,plain,
% 54.78/7.50      ( X0 != X1 | X2 != X3 | k5_xboole_0(X0,X2) = k5_xboole_0(X1,X3) ),
% 54.78/7.50      theory(equality) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_1001,plain,
% 54.78/7.50      ( X0 != X1
% 54.78/7.50      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k5_xboole_0(X1,X3)
% 54.78/7.50      | k3_xboole_0(X0,X2) != X3 ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_370]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_2850,plain,
% 54.78/7.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,X1)
% 54.78/7.50      | k3_xboole_0(sK1,sK2) != X1
% 54.78/7.50      | sK1 != X0 ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_1001]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_6124,plain,
% 54.78/7.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(X0,k3_xboole_0(sK2,sK1))
% 54.78/7.50      | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
% 54.78/7.50      | sK1 != X0 ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_2850]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_14456,plain,
% 54.78/7.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,k3_xboole_0(sK2,sK1))
% 54.78/7.50      | k3_xboole_0(sK1,sK2) != k3_xboole_0(sK2,sK1)
% 54.78/7.50      | sK1 != sK1 ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_6124]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_6125,plain,
% 54.78/7.50      ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_1]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_364,plain,( X0 = X0 ),theory(equality) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_986,plain,
% 54.78/7.50      ( sK1 = sK1 ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_364]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_4,plain,
% 54.78/7.50      ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1) ),
% 54.78/7.50      inference(cnf_transformation,[],[f32]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_874,plain,
% 54.78/7.50      ( r2_hidden(sK0(sK1,sK3),k3_xboole_0(sK1,sK3))
% 54.78/7.50      | r1_xboole_0(sK1,sK3) ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_4]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_377,plain,
% 54.78/7.50      ( k1_xboole_0 = k1_xboole_0 ),
% 54.78/7.50      inference(instantiation,[status(thm)],[c_364]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_6,plain,
% 54.78/7.50      ( r1_tarski(X0,X1)
% 54.78/7.50      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 54.78/7.50      inference(cnf_transformation,[],[f50]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_119,plain,
% 54.78/7.50      ( r1_tarski(X0,X1)
% 54.78/7.50      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 54.78/7.50      inference(prop_impl,[status(thm)],[c_6]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_17,negated_conjecture,
% 54.78/7.50      ( ~ r1_tarski(sK1,sK2) | ~ r1_xboole_0(sK1,sK3) ),
% 54.78/7.50      inference(cnf_transformation,[],[f48]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_276,plain,
% 54.78/7.50      ( ~ r1_xboole_0(sK1,sK3)
% 54.78/7.50      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 54.78/7.50      | sK2 != X1
% 54.78/7.50      | sK1 != X0 ),
% 54.78/7.50      inference(resolution_lifted,[status(thm)],[c_119,c_17]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(c_277,plain,
% 54.78/7.50      ( ~ r1_xboole_0(sK1,sK3)
% 54.78/7.50      | k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k1_xboole_0 ),
% 54.78/7.50      inference(unflattening,[status(thm)],[c_276]) ).
% 54.78/7.50  
% 54.78/7.50  cnf(contradiction,plain,
% 54.78/7.50      ( $false ),
% 54.78/7.50      inference(minisat,
% 54.78/7.50                [status(thm)],
% 54.78/7.50                [c_222269,c_218455,c_218454,c_211637,c_186673,c_125223,
% 54.78/7.50                 c_91772,c_29869,c_14456,c_6125,c_986,c_874,c_377,c_277]) ).
% 54.78/7.50  
% 54.78/7.50  
% 54.78/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 54.78/7.50  
% 54.78/7.50  ------                               Statistics
% 54.78/7.50  
% 54.78/7.50  ------ Selected
% 54.78/7.50  
% 54.78/7.50  total_time:                             6.51
% 54.78/7.50  
%------------------------------------------------------------------------------
