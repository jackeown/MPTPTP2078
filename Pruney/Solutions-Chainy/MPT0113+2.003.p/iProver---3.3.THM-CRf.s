%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:43 EST 2020

% Result     : Theorem 35.66s
% Output     : CNFRefutation 35.66s
% Verified   : 
% Statistics : Number of formulae       :  176 (5226 expanded)
%              Number of clauses        :  116 (1667 expanded)
%              Number of leaves         :   21 (1359 expanded)
%              Depth                    :   47
%              Number of atoms          :  286 (7176 expanded)
%              Number of equality atoms :  176 (4713 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f50])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f50,f50])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f50])).

fof(f13,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK2,sK4)
        | ~ r1_tarski(sK2,sK3) )
      & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( ~ r1_xboole_0(sK2,sK4)
      | ~ r1_tarski(sK2,sK3) )
    & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f33])).

fof(f56,plain,(
    r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f50])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f50])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f29])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f31])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f38,f50])).

fof(f57,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_19,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11934,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11944,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17267,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11934,c_11944])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_12,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_11939,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_11940,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_15697,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11939,c_11940])).

cnf(c_84700,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_15697,c_2])).

cnf(c_85386,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_84700])).

cnf(c_110279,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_17267,c_85386])).

cnf(c_14,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_110603,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_110279,c_14])).

cnf(c_12584,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_14,c_2])).

cnf(c_21,negated_conjecture,
    ( r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_11932,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15698,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = sK2 ),
    inference(superposition,[status(thm)],[c_11932,c_11940])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_16109,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_15698,c_0])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12431,plain,
    ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_16125,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_16109,c_12431])).

cnf(c_13,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12591,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2,c_13])).

cnf(c_23181,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)),sK2) ),
    inference(superposition,[status(thm)],[c_16125,c_12591])).

cnf(c_23257,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) ),
    inference(light_normalisation,[status(thm)],[c_23181,c_16125])).

cnf(c_18,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,X2)
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11935,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_23658,plain,
    ( r1_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,sK2),sK2)) = iProver_top
    | r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23257,c_11935])).

cnf(c_23890,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k2_xboole_0(k4_xboole_0(sK2,sK2),sK2)) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11934,c_23658])).

cnf(c_16328,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16125,c_11934])).

cnf(c_16333,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) ),
    inference(superposition,[status(thm)],[c_16125,c_13])).

cnf(c_16557,plain,
    ( r1_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK3,sK4),sK2)) = iProver_top
    | r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16333,c_11935])).

cnf(c_18273,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k1_xboole_0
    | r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16557,c_11944])).

cnf(c_27183,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k1_xboole_0
    | r1_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16328,c_18273])).

cnf(c_12745,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_11939])).

cnf(c_13151,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_12745])).

cnf(c_16323,plain,
    ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16125,c_13151])).

cnf(c_16755,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) ),
    inference(superposition,[status(thm)],[c_16323,c_11940])).

cnf(c_12603,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_11934])).

cnf(c_18426,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))))),k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_16755,c_12603])).

cnf(c_18407,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)))),k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) ),
    inference(superposition,[status(thm)],[c_2,c_16755])).

cnf(c_18467,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))),k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) ),
    inference(light_normalisation,[status(thm)],[c_18407,c_16125])).

cnf(c_13026,plain,
    ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_12584,c_11939])).

cnf(c_15701,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_13026,c_11940])).

cnf(c_15712,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
    inference(demodulation,[status(thm)],[c_15701,c_14])).

cnf(c_18468,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k4_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_18467,c_5,c_15712])).

cnf(c_18501,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,sK2))),k4_xboole_0(sK2,sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18426,c_18468])).

cnf(c_18502,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18501,c_15712])).

cnf(c_27226,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27183,c_18502])).

cnf(c_27247,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k4_xboole_0(sK3,sK4),sK2)) = k5_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_27226,c_0])).

cnf(c_27322,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK2),k5_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27247,c_27226])).

cnf(c_27454,plain,
    ( k5_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK2,sK2),k5_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_27322,c_0])).

cnf(c_27494,plain,
    ( k5_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_27454,c_27322])).

cnf(c_12590,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_13462,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k4_xboole_0(X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_5,c_12590])).

cnf(c_27496,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK2),sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27494,c_14,c_13462])).

cnf(c_27972,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_27496,c_13])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_27989,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_27972,c_10,c_13])).

cnf(c_28200,plain,
    ( k2_xboole_0(sK2,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_27989,c_13])).

cnf(c_18564,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),sK2) ),
    inference(superposition,[status(thm)],[c_18468,c_13])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_24681,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),sK2) ),
    inference(superposition,[status(thm)],[c_18564,c_1])).

cnf(c_24707,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) ),
    inference(light_normalisation,[status(thm)],[c_24681,c_23257])).

cnf(c_24800,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_2,c_24707])).

cnf(c_24822,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) ),
    inference(light_normalisation,[status(thm)],[c_24800,c_16125])).

cnf(c_24823,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) = k2_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_24822,c_5])).

cnf(c_28225,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_28200,c_24823])).

cnf(c_31081,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)) != iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23890,c_28225])).

cnf(c_31089,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),sK2) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)))),k4_xboole_0(sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_31081])).

cnf(c_31093,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),sK2) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))),k4_xboole_0(sK2,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31089,c_16125])).

cnf(c_31094,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),sK2) = iProver_top
    | r1_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31093,c_5])).

cnf(c_31108,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),sK2),k4_xboole_0(sK2,sK2)) != iProver_top
    | r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_12584,c_31094])).

cnf(c_31314,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))),sK2),k4_xboole_0(sK2,sK2)) != iProver_top
    | r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_31108])).

cnf(c_31316,plain,
    ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),sK2),k4_xboole_0(sK2,sK2)) != iProver_top
    | r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31314,c_16125])).

cnf(c_31317,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)) != iProver_top
    | r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_31316,c_5])).

cnf(c_31320,plain,
    ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31317,c_18502])).

cnf(c_31327,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_31320,c_11944])).

cnf(c_31480,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))))),sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_31327])).

cnf(c_31633,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)))),sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_31480,c_16125])).

cnf(c_31634,plain,
    ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)),sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31633,c_5])).

cnf(c_31690,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_31634,c_2])).

cnf(c_13040,plain,
    ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_12584,c_5])).

cnf(c_32297,plain,
    ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_31690,c_13040])).

cnf(c_45123,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) ),
    inference(demodulation,[status(thm)],[c_32297,c_16333])).

cnf(c_45129,plain,
    ( k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) = k4_xboole_0(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_45123,c_10])).

cnf(c_16,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11937,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_46046,plain,
    ( r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_45129,c_11937])).

cnf(c_53263,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK3,sK4)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_11934,c_46046])).

cnf(c_110970,plain,
    ( r1_xboole_0(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_110603,c_53263])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_11941,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16899,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_11941])).

cnf(c_46047,plain,
    ( r1_tarski(k4_xboole_0(sK3,sK4),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_45129,c_16899])).

cnf(c_53289,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_11939,c_46047])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9459,plain,
    ( ~ r2_hidden(sK1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))
    | ~ r1_xboole_0(sK4,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9460,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top
    | r1_xboole_0(sK4,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9459])).

cnf(c_9277,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7450,plain,
    ( r2_hidden(sK1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))
    | k1_xboole_0 = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7451,plain,
    ( k1_xboole_0 = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))
    | r2_hidden(sK1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7450])).

cnf(c_194,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7386,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != X0
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_194])).

cnf(c_7432,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_7386])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1771,plain,
    ( r1_xboole_0(sK2,sK4)
    | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1772,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k1_xboole_0
    | r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1771])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_110970,c_53289,c_9460,c_9277,c_7451,c_7432,c_1772,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:54:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.66/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.66/5.00  
% 35.66/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.66/5.00  
% 35.66/5.00  ------  iProver source info
% 35.66/5.00  
% 35.66/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.66/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.66/5.00  git: non_committed_changes: false
% 35.66/5.00  git: last_make_outside_of_git: false
% 35.66/5.00  
% 35.66/5.00  ------ 
% 35.66/5.00  ------ Parsing...
% 35.66/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  ------ Proving...
% 35.66/5.00  ------ Problem Properties 
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  clauses                                 22
% 35.66/5.00  conjectures                             2
% 35.66/5.00  EPR                                     2
% 35.66/5.00  Horn                                    20
% 35.66/5.00  unary                                   11
% 35.66/5.00  binary                                  10
% 35.66/5.00  lits                                    34
% 35.66/5.00  lits eq                                 11
% 35.66/5.00  fd_pure                                 0
% 35.66/5.00  fd_pseudo                               0
% 35.66/5.00  fd_cond                                 1
% 35.66/5.00  fd_pseudo_cond                          0
% 35.66/5.00  AC symbols                              0
% 35.66/5.00  
% 35.66/5.00  ------ Input Options Time Limit: Unbounded
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing...
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 35.66/5.00  Current options:
% 35.66/5.00  ------ 
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 35.66/5.00  
% 35.66/5.00  ------ Proving...
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  % SZS status Theorem for theBenchmark.p
% 35.66/5.00  
% 35.66/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.66/5.00  
% 35.66/5.00  fof(f17,axiom,(
% 35.66/5.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f55,plain,(
% 35.66/5.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 35.66/5.00    inference(cnf_transformation,[],[f17])).
% 35.66/5.00  
% 35.66/5.00  fof(f3,axiom,(
% 35.66/5.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f28,plain,(
% 35.66/5.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.66/5.00    inference(nnf_transformation,[],[f3])).
% 35.66/5.00  
% 35.66/5.00  fof(f37,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.66/5.00    inference(cnf_transformation,[],[f28])).
% 35.66/5.00  
% 35.66/5.00  fof(f14,axiom,(
% 35.66/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f50,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.66/5.00    inference(cnf_transformation,[],[f14])).
% 35.66/5.00  
% 35.66/5.00  fof(f61,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 35.66/5.00    inference(definition_unfolding,[],[f37,f50])).
% 35.66/5.00  
% 35.66/5.00  fof(f2,axiom,(
% 35.66/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f36,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.66/5.00    inference(cnf_transformation,[],[f2])).
% 35.66/5.00  
% 35.66/5.00  fof(f59,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 35.66/5.00    inference(definition_unfolding,[],[f36,f50,f50])).
% 35.66/5.00  
% 35.66/5.00  fof(f11,axiom,(
% 35.66/5.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f47,plain,(
% 35.66/5.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.66/5.00    inference(cnf_transformation,[],[f11])).
% 35.66/5.00  
% 35.66/5.00  fof(f10,axiom,(
% 35.66/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f25,plain,(
% 35.66/5.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.66/5.00    inference(ennf_transformation,[],[f10])).
% 35.66/5.00  
% 35.66/5.00  fof(f46,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.66/5.00    inference(cnf_transformation,[],[f25])).
% 35.66/5.00  
% 35.66/5.00  fof(f65,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 35.66/5.00    inference(definition_unfolding,[],[f46,f50])).
% 35.66/5.00  
% 35.66/5.00  fof(f13,axiom,(
% 35.66/5.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f49,plain,(
% 35.66/5.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.66/5.00    inference(cnf_transformation,[],[f13])).
% 35.66/5.00  
% 35.66/5.00  fof(f18,conjecture,(
% 35.66/5.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f19,negated_conjecture,(
% 35.66/5.00    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 35.66/5.00    inference(negated_conjecture,[],[f18])).
% 35.66/5.00  
% 35.66/5.00  fof(f27,plain,(
% 35.66/5.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 35.66/5.00    inference(ennf_transformation,[],[f19])).
% 35.66/5.00  
% 35.66/5.00  fof(f33,plain,(
% 35.66/5.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4)))),
% 35.66/5.00    introduced(choice_axiom,[])).
% 35.66/5.00  
% 35.66/5.00  fof(f34,plain,(
% 35.66/5.00    (~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 35.66/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f27,f33])).
% 35.66/5.00  
% 35.66/5.00  fof(f56,plain,(
% 35.66/5.00    r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 35.66/5.00    inference(cnf_transformation,[],[f34])).
% 35.66/5.00  
% 35.66/5.00  fof(f7,axiom,(
% 35.66/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f43,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.66/5.00    inference(cnf_transformation,[],[f7])).
% 35.66/5.00  
% 35.66/5.00  fof(f58,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 35.66/5.00    inference(definition_unfolding,[],[f43,f50])).
% 35.66/5.00  
% 35.66/5.00  fof(f4,axiom,(
% 35.66/5.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f20,plain,(
% 35.66/5.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 35.66/5.00    inference(rectify,[],[f4])).
% 35.66/5.00  
% 35.66/5.00  fof(f39,plain,(
% 35.66/5.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 35.66/5.00    inference(cnf_transformation,[],[f20])).
% 35.66/5.00  
% 35.66/5.00  fof(f62,plain,(
% 35.66/5.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 35.66/5.00    inference(definition_unfolding,[],[f39,f50])).
% 35.66/5.00  
% 35.66/5.00  fof(f12,axiom,(
% 35.66/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f48,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 35.66/5.00    inference(cnf_transformation,[],[f12])).
% 35.66/5.00  
% 35.66/5.00  fof(f16,axiom,(
% 35.66/5.00    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f26,plain,(
% 35.66/5.00    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 35.66/5.00    inference(ennf_transformation,[],[f16])).
% 35.66/5.00  
% 35.66/5.00  fof(f52,plain,(
% 35.66/5.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 35.66/5.00    inference(cnf_transformation,[],[f26])).
% 35.66/5.00  
% 35.66/5.00  fof(f9,axiom,(
% 35.66/5.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f45,plain,(
% 35.66/5.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.66/5.00    inference(cnf_transformation,[],[f9])).
% 35.66/5.00  
% 35.66/5.00  fof(f1,axiom,(
% 35.66/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f35,plain,(
% 35.66/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 35.66/5.00    inference(cnf_transformation,[],[f1])).
% 35.66/5.00  
% 35.66/5.00  fof(f54,plain,(
% 35.66/5.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 35.66/5.00    inference(cnf_transformation,[],[f26])).
% 35.66/5.00  
% 35.66/5.00  fof(f8,axiom,(
% 35.66/5.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f24,plain,(
% 35.66/5.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 35.66/5.00    inference(ennf_transformation,[],[f8])).
% 35.66/5.00  
% 35.66/5.00  fof(f44,plain,(
% 35.66/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 35.66/5.00    inference(cnf_transformation,[],[f24])).
% 35.66/5.00  
% 35.66/5.00  fof(f5,axiom,(
% 35.66/5.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f21,plain,(
% 35.66/5.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 35.66/5.00    inference(rectify,[],[f5])).
% 35.66/5.00  
% 35.66/5.00  fof(f22,plain,(
% 35.66/5.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.66/5.00    inference(ennf_transformation,[],[f21])).
% 35.66/5.00  
% 35.66/5.00  fof(f29,plain,(
% 35.66/5.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 35.66/5.00    introduced(choice_axiom,[])).
% 35.66/5.00  
% 35.66/5.00  fof(f30,plain,(
% 35.66/5.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 35.66/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f29])).
% 35.66/5.00  
% 35.66/5.00  fof(f41,plain,(
% 35.66/5.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 35.66/5.00    inference(cnf_transformation,[],[f30])).
% 35.66/5.00  
% 35.66/5.00  fof(f63,plain,(
% 35.66/5.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 35.66/5.00    inference(definition_unfolding,[],[f41,f50])).
% 35.66/5.00  
% 35.66/5.00  fof(f6,axiom,(
% 35.66/5.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 35.66/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.66/5.00  
% 35.66/5.00  fof(f23,plain,(
% 35.66/5.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 35.66/5.00    inference(ennf_transformation,[],[f6])).
% 35.66/5.00  
% 35.66/5.00  fof(f31,plain,(
% 35.66/5.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 35.66/5.00    introduced(choice_axiom,[])).
% 35.66/5.00  
% 35.66/5.00  fof(f32,plain,(
% 35.66/5.00    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 35.66/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f31])).
% 35.66/5.00  
% 35.66/5.00  fof(f42,plain,(
% 35.66/5.00    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 35.66/5.00    inference(cnf_transformation,[],[f32])).
% 35.66/5.00  
% 35.66/5.00  fof(f38,plain,(
% 35.66/5.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.66/5.00    inference(cnf_transformation,[],[f28])).
% 35.66/5.00  
% 35.66/5.00  fof(f60,plain,(
% 35.66/5.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.66/5.00    inference(definition_unfolding,[],[f38,f50])).
% 35.66/5.00  
% 35.66/5.00  fof(f57,plain,(
% 35.66/5.00    ~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)),
% 35.66/5.00    inference(cnf_transformation,[],[f34])).
% 35.66/5.00  
% 35.66/5.00  cnf(c_19,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 35.66/5.00      inference(cnf_transformation,[],[f55]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_11934,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_4,plain,
% 35.66/5.00      ( ~ r1_xboole_0(X0,X1)
% 35.66/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 35.66/5.00      inference(cnf_transformation,[],[f61]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_11944,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 35.66/5.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_17267,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_11934,c_11944]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_2,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 35.66/5.00      inference(cnf_transformation,[],[f59]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_12,plain,
% 35.66/5.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 35.66/5.00      inference(cnf_transformation,[],[f47]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_11939,plain,
% 35.66/5.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_11,plain,
% 35.66/5.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 35.66/5.00      inference(cnf_transformation,[],[f65]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_11940,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 35.66/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_15697,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_11939,c_11940]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_84700,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_15697,c_2]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_85386,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_84700]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_110279,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_17267,c_85386]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_14,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.66/5.00      inference(cnf_transformation,[],[f49]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_110603,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_110279,c_14]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_12584,plain,
% 35.66/5.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_14,c_2]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_21,negated_conjecture,
% 35.66/5.00      ( r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
% 35.66/5.00      inference(cnf_transformation,[],[f56]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_11932,plain,
% 35.66/5.00      ( r1_tarski(sK2,k4_xboole_0(sK3,sK4)) = iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_15698,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))) = sK2 ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_11932,c_11940]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_0,plain,
% 35.66/5.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 35.66/5.00      inference(cnf_transformation,[],[f58]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_16109,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k5_xboole_0(sK2,sK2) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_15698,c_0]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_5,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 35.66/5.00      inference(cnf_transformation,[],[f62]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_12431,plain,
% 35.66/5.00      ( k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_16125,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)) = k4_xboole_0(sK2,sK2) ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_16109,c_12431]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_13,plain,
% 35.66/5.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 35.66/5.00      inference(cnf_transformation,[],[f48]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_12591,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_13]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_23181,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)),sK2) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_16125,c_12591]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_23257,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_23181,c_16125]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_18,plain,
% 35.66/5.00      ( ~ r1_xboole_0(X0,X1)
% 35.66/5.00      | ~ r1_xboole_0(X0,X2)
% 35.66/5.00      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 35.66/5.00      inference(cnf_transformation,[],[f52]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_11935,plain,
% 35.66/5.00      ( r1_xboole_0(X0,X1) != iProver_top
% 35.66/5.00      | r1_xboole_0(X0,X2) != iProver_top
% 35.66/5.00      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_23658,plain,
% 35.66/5.00      ( r1_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK2,sK2),sK2)) = iProver_top
% 35.66/5.00      | r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) != iProver_top
% 35.66/5.00      | r1_xboole_0(X0,k4_xboole_0(sK2,sK2)) != iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_23257,c_11935]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_23890,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k2_xboole_0(k4_xboole_0(sK2,sK2),sK2)) = iProver_top
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)) != iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_11934,c_23658]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_16328,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK3,sK4)) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_16125,c_11934]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_16333,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_16125,c_13]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_16557,plain,
% 35.66/5.00      ( r1_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK3,sK4),sK2)) = iProver_top
% 35.66/5.00      | r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) != iProver_top
% 35.66/5.00      | r1_xboole_0(X0,k4_xboole_0(sK2,sK2)) != iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_16333,c_11935]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_18273,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k1_xboole_0
% 35.66/5.00      | r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) != iProver_top
% 35.66/5.00      | r1_xboole_0(X0,k4_xboole_0(sK2,sK2)) != iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_16557,c_11944]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_27183,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k1_xboole_0
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)) != iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_16328,c_18273]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_12745,plain,
% 35.66/5.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_11939]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_13151,plain,
% 35.66/5.00      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_12745]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_16323,plain,
% 35.66/5.00      ( r1_tarski(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_16125,c_13151]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_16755,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_16323,c_11940]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_12603,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_11934]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_18426,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))))),k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_16755,c_12603]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_18407,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)))),k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_16755]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_18467,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))),k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))),k4_xboole_0(sK2,sK2))) = k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_18407,c_16125]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_13026,plain,
% 35.66/5.00      ( r1_tarski(k4_xboole_0(X0,X0),k1_xboole_0) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_12584,c_11939]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_15701,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_13026,c_11940]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_15712,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(X0,X0) ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_15701,c_14]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_18468,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k4_xboole_0(sK2,sK2) ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_18467,c_5,c_15712]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_18501,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)),k4_xboole_0(sK2,sK2))),k4_xboole_0(sK2,sK2)) = iProver_top ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_18426,c_18468]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_18502,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)) = iProver_top ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_18501,c_15712]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_27226,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k1_xboole_0 ),
% 35.66/5.00      inference(global_propositional_subsumption,
% 35.66/5.00                [status(thm)],
% 35.66/5.00                [c_27183,c_18502]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_27247,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(sK2,sK2),k2_xboole_0(k4_xboole_0(sK3,sK4),sK2)) = k5_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_27226,c_0]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_27322,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(sK2,sK2),k5_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0)) = k1_xboole_0 ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_27247,c_27226]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_27454,plain,
% 35.66/5.00      ( k5_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(sK2,sK2),k5_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0)) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_27322,c_0]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_27494,plain,
% 35.66/5.00      ( k5_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK2,sK2),k1_xboole_0)) = k1_xboole_0 ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_27454,c_27322]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_12590,plain,
% 35.66/5.00      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_13462,plain,
% 35.66/5.00      ( k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = k4_xboole_0(k4_xboole_0(X0,X0),X0) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_5,c_12590]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_27496,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(sK2,sK2),sK2) = k1_xboole_0 ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_27494,c_14,c_13462]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_27972,plain,
% 35.66/5.00      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = k2_xboole_0(sK2,k1_xboole_0) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_27496,c_13]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_10,plain,
% 35.66/5.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.66/5.00      inference(cnf_transformation,[],[f45]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_27989,plain,
% 35.66/5.00      ( k2_xboole_0(sK2,k4_xboole_0(sK2,sK2)) = sK2 ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_27972,c_10,c_13]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_28200,plain,
% 35.66/5.00      ( k2_xboole_0(sK2,sK2) = sK2 ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_27989,c_13]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_18564,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),k4_xboole_0(sK2,sK2)) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),sK2) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_18468,c_13]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_1,plain,
% 35.66/5.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 35.66/5.00      inference(cnf_transformation,[],[f35]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_24681,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),sK2) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_18564,c_1]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_24707,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_24681,c_23257]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_24800,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_24707]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_24822,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_24800,c_16125]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_24823,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) = k2_xboole_0(sK2,sK2) ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_24822,c_5]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_28225,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) = sK2 ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_28200,c_24823]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31081,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),k4_xboole_0(sK2,sK2)) != iProver_top
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),sK2) = iProver_top ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_23890,c_28225]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31089,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),sK2) = iProver_top
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4)))),k4_xboole_0(sK2,sK2)) != iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_31081]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31093,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),sK2) = iProver_top
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))),k4_xboole_0(sK2,sK2)) != iProver_top ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_31089,c_16125]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31094,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2))),sK2) = iProver_top
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(X0,sK2),k4_xboole_0(sK2,sK2)) != iProver_top ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_31093,c_5]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31108,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)),sK2),k4_xboole_0(sK2,sK2)) != iProver_top
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_12584,c_31094]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31314,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))),sK2),k4_xboole_0(sK2,sK2)) != iProver_top
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_31108]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31316,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)),sK2),k4_xboole_0(sK2,sK2)) != iProver_top
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_31314,c_16125]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31317,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(sK2,sK2),k4_xboole_0(sK2,sK2)) != iProver_top
% 35.66/5.00      | r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_31316,c_5]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31320,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2) = iProver_top ),
% 35.66/5.00      inference(global_propositional_subsumption,
% 35.66/5.00                [status(thm)],
% 35.66/5.00                [c_31317,c_18502]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31327,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK3,sK4),k4_xboole_0(k4_xboole_0(sK3,sK4),sK2)))),sK2)) = k1_xboole_0 ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_31320,c_11944]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31480,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK3,sK4))))),sK2)) = k1_xboole_0 ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_2,c_31327]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31633,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)))),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)))),sK2)) = k1_xboole_0 ),
% 35.66/5.00      inference(light_normalisation,[status(thm)],[c_31480,c_16125]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31634,plain,
% 35.66/5.00      ( k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)),k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)),sK2)) = k1_xboole_0 ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_31633,c_5]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_31690,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)))) = k1_xboole_0 ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_31634,c_2]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_13040,plain,
% 35.66/5.00      ( k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) = X0 ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_12584,c_5]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_32297,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,sK2) = k1_xboole_0 ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_31690,c_13040]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_45123,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK3,sK4),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_32297,c_16333]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_45129,plain,
% 35.66/5.00      ( k2_xboole_0(k4_xboole_0(sK3,sK4),sK2) = k4_xboole_0(sK3,sK4) ),
% 35.66/5.00      inference(demodulation,[status(thm)],[c_45123,c_10]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_16,plain,
% 35.66/5.00      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X2,X1)) ),
% 35.66/5.00      inference(cnf_transformation,[],[f54]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_11937,plain,
% 35.66/5.00      ( r1_xboole_0(X0,X1) = iProver_top
% 35.66/5.00      | r1_xboole_0(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_46046,plain,
% 35.66/5.00      ( r1_xboole_0(X0,k4_xboole_0(sK3,sK4)) != iProver_top
% 35.66/5.00      | r1_xboole_0(X0,sK2) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_45129,c_11937]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_53263,plain,
% 35.66/5.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(sK3,sK4)),sK2) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_11934,c_46046]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_110970,plain,
% 35.66/5.00      ( r1_xboole_0(sK4,sK2) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_110603,c_53263]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_9,plain,
% 35.66/5.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 35.66/5.00      inference(cnf_transformation,[],[f44]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_11941,plain,
% 35.66/5.00      ( r1_tarski(X0,X1) = iProver_top
% 35.66/5.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_16899,plain,
% 35.66/5.00      ( r1_tarski(X0,X1) = iProver_top
% 35.66/5.00      | r1_tarski(k2_xboole_0(X2,X0),X1) != iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_1,c_11941]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_46047,plain,
% 35.66/5.00      ( r1_tarski(k4_xboole_0(sK3,sK4),X0) != iProver_top
% 35.66/5.00      | r1_tarski(sK2,X0) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_45129,c_16899]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_53289,plain,
% 35.66/5.00      ( r1_tarski(sK2,sK3) = iProver_top ),
% 35.66/5.00      inference(superposition,[status(thm)],[c_11939,c_46047]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_6,plain,
% 35.66/5.00      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 35.66/5.00      | ~ r1_xboole_0(X1,X2) ),
% 35.66/5.00      inference(cnf_transformation,[],[f63]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_9459,plain,
% 35.66/5.00      ( ~ r2_hidden(sK1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))
% 35.66/5.00      | ~ r1_xboole_0(sK4,sK2) ),
% 35.66/5.00      inference(instantiation,[status(thm)],[c_6]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_9460,plain,
% 35.66/5.00      ( r2_hidden(sK1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) != iProver_top
% 35.66/5.00      | r1_xboole_0(sK4,sK2) != iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_9459]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_9277,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
% 35.66/5.00      inference(instantiation,[status(thm)],[c_2]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_8,plain,
% 35.66/5.00      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 35.66/5.00      inference(cnf_transformation,[],[f42]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_7450,plain,
% 35.66/5.00      ( r2_hidden(sK1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)))
% 35.66/5.00      | k1_xboole_0 = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
% 35.66/5.00      inference(instantiation,[status(thm)],[c_8]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_7451,plain,
% 35.66/5.00      ( k1_xboole_0 = k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))
% 35.66/5.00      | r2_hidden(sK1(k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))),k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))) = iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_7450]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_194,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_7386,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != X0
% 35.66/5.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0
% 35.66/5.00      | k1_xboole_0 != X0 ),
% 35.66/5.00      inference(instantiation,[status(thm)],[c_194]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_7432,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2))
% 35.66/5.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0
% 35.66/5.00      | k1_xboole_0 != k4_xboole_0(sK4,k4_xboole_0(sK4,sK2)) ),
% 35.66/5.00      inference(instantiation,[status(thm)],[c_7386]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_3,plain,
% 35.66/5.00      ( r1_xboole_0(X0,X1)
% 35.66/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 35.66/5.00      inference(cnf_transformation,[],[f60]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_1771,plain,
% 35.66/5.00      ( r1_xboole_0(sK2,sK4)
% 35.66/5.00      | k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k1_xboole_0 ),
% 35.66/5.00      inference(instantiation,[status(thm)],[c_3]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_1772,plain,
% 35.66/5.00      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) != k1_xboole_0
% 35.66/5.00      | r1_xboole_0(sK2,sK4) = iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_1771]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_20,negated_conjecture,
% 35.66/5.00      ( ~ r1_tarski(sK2,sK3) | ~ r1_xboole_0(sK2,sK4) ),
% 35.66/5.00      inference(cnf_transformation,[],[f57]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(c_23,plain,
% 35.66/5.00      ( r1_tarski(sK2,sK3) != iProver_top
% 35.66/5.00      | r1_xboole_0(sK2,sK4) != iProver_top ),
% 35.66/5.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 35.66/5.00  
% 35.66/5.00  cnf(contradiction,plain,
% 35.66/5.00      ( $false ),
% 35.66/5.00      inference(minisat,
% 35.66/5.00                [status(thm)],
% 35.66/5.00                [c_110970,c_53289,c_9460,c_9277,c_7451,c_7432,c_1772,
% 35.66/5.00                 c_23]) ).
% 35.66/5.00  
% 35.66/5.00  
% 35.66/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.66/5.00  
% 35.66/5.00  ------                               Statistics
% 35.66/5.00  
% 35.66/5.00  ------ Selected
% 35.66/5.00  
% 35.66/5.00  total_time:                             4.165
% 35.66/5.00  
%------------------------------------------------------------------------------
