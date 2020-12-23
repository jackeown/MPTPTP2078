%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:58 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 195 expanded)
%              Number of leaves         :   17 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  198 ( 417 expanded)
%              Number of equality atoms :  157 ( 354 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(subsumption_resolution,[],[f370,f29])).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f370,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f367,f76])).

fof(f76,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

% (18646)Refutation not found, incomplete strategy% (18646)------------------------------
% (18646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

% (18646)Termination reason: Refutation not found, incomplete strategy
fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f23])).

% (18646)Memory used [KB]: 10618
% (18646)Time elapsed: 0.069 s
fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f367,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK1))
      | sK1 = X0 ) ),
    inference(duplicate_literal_removal,[],[f361])).

fof(f361,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK1))
      | sK1 = X0
      | sK1 = X0
      | sK1 = X0 ) ),
    inference(superposition,[],[f77,f349])).

fof(f349,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_enumset1(sK0,sK0,sK0,sK1,sK1) ),
    inference(superposition,[],[f348,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f348,plain,(
    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k3_enumset1(sK0,sK0,sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f344,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f41,f52,f52])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f344,plain,(
    k3_enumset1(sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f59,f183])).

fof(f183,plain,(
    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f101,f135])).

fof(f135,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f99,f119])).

fof(f119,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(backward_demodulation,[],[f85,f110])).

fof(f110,plain,(
    ! [X0] : k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f57,f99])).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f85,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X3,X3))) ),
    inference(resolution,[],[f61,f79])).

fof(f79,plain,(
    ! [X0] : r1_xboole_0(X0,k5_xboole_0(X0,X0)) ),
    inference(superposition,[],[f58,f57])).

fof(f58,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f99,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f55,f57])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f101,plain,(
    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f55,f56])).

fof(f56,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f28,f54,f38,f54,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f36,f53,f35,f54,f54])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f77,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f52])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.08  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n001.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 11:15:29 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.12/0.34  % (18637)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.12/0.35  % (18639)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.12/0.35  % (18653)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.12/0.35  % (18651)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.12/0.35  % (18641)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.12/0.36  % (18640)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.12/0.36  % (18646)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.12/0.36  % (18636)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.12/0.36  % (18638)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.12/0.36  % (18658)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.12/0.36  % (18645)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.12/0.36  % (18635)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.12/0.37  % (18661)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.12/0.37  % (18650)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.12/0.37  % (18638)Refutation found. Thanks to Tanya!
% 0.12/0.37  % SZS status Theorem for theBenchmark
% 0.12/0.37  % SZS output start Proof for theBenchmark
% 0.12/0.37  fof(f371,plain,(
% 0.12/0.37    $false),
% 0.12/0.37    inference(subsumption_resolution,[],[f370,f29])).
% 0.12/0.37  fof(f29,plain,(
% 0.12/0.37    sK0 != sK1),
% 0.12/0.37    inference(cnf_transformation,[],[f21])).
% 0.12/0.37  fof(f21,plain,(
% 0.12/0.37    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.12/0.37    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 0.12/0.37  fof(f20,plain,(
% 0.12/0.37    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.12/0.37    introduced(choice_axiom,[])).
% 0.12/0.37  fof(f18,plain,(
% 0.12/0.37    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.12/0.37    inference(ennf_transformation,[],[f16])).
% 0.12/0.37  fof(f16,negated_conjecture,(
% 0.12/0.37    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.12/0.37    inference(negated_conjecture,[],[f15])).
% 0.12/0.37  fof(f15,conjecture,(
% 0.12/0.37    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.12/0.37  fof(f370,plain,(
% 0.12/0.37    sK0 = sK1),
% 0.12/0.37    inference(resolution,[],[f367,f76])).
% 0.12/0.37  fof(f76,plain,(
% 0.12/0.37    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 0.12/0.37    inference(equality_resolution,[],[f75])).
% 0.12/0.37  fof(f75,plain,(
% 0.12/0.37    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 0.12/0.37    inference(equality_resolution,[],[f69])).
% 0.12/0.37  fof(f69,plain,(
% 0.12/0.37    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.12/0.37    inference(definition_unfolding,[],[f45,f52])).
% 0.12/0.37  fof(f52,plain,(
% 0.12/0.37    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.12/0.37    inference(definition_unfolding,[],[f42,f43])).
% 0.12/0.37  fof(f43,plain,(
% 0.12/0.37    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f14])).
% 0.12/0.37  fof(f14,axiom,(
% 0.12/0.37    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.12/0.37  fof(f42,plain,(
% 0.12/0.37    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f13])).
% 0.12/0.37  fof(f13,axiom,(
% 0.12/0.37    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.12/0.37  fof(f45,plain,(
% 0.12/0.37    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.12/0.37    inference(cnf_transformation,[],[f27])).
% 0.12/0.37  fof(f27,plain,(
% 0.12/0.37    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.12/0.37    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 0.12/0.37  % (18646)Refutation not found, incomplete strategy% (18646)------------------------------
% 0.12/0.37  % (18646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.37  fof(f26,plain,(
% 0.12/0.37    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 0.12/0.37    introduced(choice_axiom,[])).
% 0.12/0.37  % (18646)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.37  fof(f25,plain,(
% 0.12/0.37    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.12/0.37    inference(rectify,[],[f24])).
% 0.12/0.37  
% 0.12/0.37  fof(f24,plain,(
% 0.12/0.37    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.12/0.37    inference(flattening,[],[f23])).
% 0.12/0.37  % (18646)Memory used [KB]: 10618
% 0.12/0.37  % (18646)Time elapsed: 0.069 s
% 0.12/0.37  fof(f23,plain,(
% 0.12/0.37    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.12/0.37    inference(nnf_transformation,[],[f19])).
% 0.12/0.37  fof(f19,plain,(
% 0.12/0.37    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.12/0.37    inference(ennf_transformation,[],[f8])).
% 0.12/0.37  fof(f8,axiom,(
% 0.12/0.37    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.12/0.37  fof(f367,plain,(
% 0.12/0.37    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK1)) | sK1 = X0) )),
% 0.12/0.37    inference(duplicate_literal_removal,[],[f361])).
% 0.12/0.37  fof(f361,plain,(
% 0.12/0.37    ( ! [X0] : (~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK1,sK1)) | sK1 = X0 | sK1 = X0 | sK1 = X0) )),
% 0.12/0.37    inference(superposition,[],[f77,f349])).
% 0.12/0.37  fof(f349,plain,(
% 0.12/0.37    k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k3_enumset1(sK0,sK0,sK0,sK1,sK1)),
% 0.12/0.37    inference(superposition,[],[f348,f30])).
% 0.12/0.37  fof(f30,plain,(
% 0.12/0.37    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.12/0.37    inference(cnf_transformation,[],[f6])).
% 0.12/0.37  fof(f6,axiom,(
% 0.12/0.37    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.12/0.37  fof(f348,plain,(
% 0.12/0.37    k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k3_enumset1(sK0,sK0,sK0,sK1,sK1)),
% 0.12/0.37    inference(forward_demodulation,[],[f344,f62])).
% 0.12/0.37  fof(f62,plain,(
% 0.12/0.37    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k3_enumset1(X2,X2,X2,X1,X0)) )),
% 0.12/0.37    inference(definition_unfolding,[],[f41,f52,f52])).
% 0.12/0.37  fof(f41,plain,(
% 0.12/0.37    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f9])).
% 0.12/0.37  fof(f9,axiom,(
% 0.12/0.37    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 0.12/0.37  fof(f344,plain,(
% 0.12/0.37    k3_enumset1(sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k1_xboole_0)),
% 0.12/0.37    inference(superposition,[],[f59,f183])).
% 0.12/0.37  fof(f183,plain,(
% 0.12/0.37    k1_xboole_0 = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.12/0.37    inference(forward_demodulation,[],[f101,f135])).
% 0.12/0.37  fof(f135,plain,(
% 0.12/0.37    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.12/0.37    inference(backward_demodulation,[],[f99,f119])).
% 0.12/0.37  fof(f119,plain,(
% 0.12/0.37    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 0.12/0.37    inference(backward_demodulation,[],[f85,f110])).
% 0.12/0.37  fof(f110,plain,(
% 0.12/0.37    ( ! [X0] : (k4_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 0.12/0.37    inference(backward_demodulation,[],[f57,f99])).
% 0.12/0.37  fof(f57,plain,(
% 0.12/0.37    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.12/0.37    inference(definition_unfolding,[],[f32,f38])).
% 0.12/0.37  fof(f38,plain,(
% 0.12/0.37    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.12/0.37    inference(cnf_transformation,[],[f5])).
% 0.12/0.37  fof(f5,axiom,(
% 0.12/0.37    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.12/0.37  fof(f32,plain,(
% 0.12/0.37    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.12/0.37    inference(cnf_transformation,[],[f17])).
% 0.12/0.37  fof(f17,plain,(
% 0.12/0.37    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.12/0.37    inference(rectify,[],[f2])).
% 0.12/0.37  fof(f2,axiom,(
% 0.12/0.37    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.12/0.37  fof(f85,plain,(
% 0.12/0.37    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X3,X3)))) )),
% 0.12/0.37    inference(resolution,[],[f61,f79])).
% 0.12/0.37  fof(f79,plain,(
% 0.12/0.37    ( ! [X0] : (r1_xboole_0(X0,k5_xboole_0(X0,X0))) )),
% 0.12/0.37    inference(superposition,[],[f58,f57])).
% 0.12/0.37  fof(f58,plain,(
% 0.12/0.37    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X0,X1))) )),
% 0.12/0.37    inference(definition_unfolding,[],[f33,f38])).
% 0.12/0.37  fof(f33,plain,(
% 0.12/0.37    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.12/0.37    inference(cnf_transformation,[],[f3])).
% 0.12/0.37  fof(f3,axiom,(
% 0.12/0.37    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.12/0.37  fof(f61,plain,(
% 0.12/0.37    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.12/0.37    inference(definition_unfolding,[],[f39,f38])).
% 0.12/0.37  fof(f39,plain,(
% 0.12/0.37    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f22])).
% 0.12/0.37  fof(f22,plain,(
% 0.12/0.37    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.12/0.37    inference(nnf_transformation,[],[f1])).
% 0.12/0.37  fof(f1,axiom,(
% 0.12/0.37    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.12/0.37  fof(f99,plain,(
% 0.12/0.37    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.12/0.37    inference(superposition,[],[f55,f57])).
% 0.12/0.37  fof(f55,plain,(
% 0.12/0.37    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.12/0.37    inference(definition_unfolding,[],[f37,f38])).
% 0.12/0.37  fof(f37,plain,(
% 0.12/0.37    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.12/0.37    inference(cnf_transformation,[],[f4])).
% 0.12/0.37  fof(f4,axiom,(
% 0.12/0.37    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.12/0.37  fof(f101,plain,(
% 0.12/0.37    k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.12/0.37    inference(superposition,[],[f55,f56])).
% 0.12/0.37  fof(f56,plain,(
% 0.12/0.37    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.12/0.37    inference(definition_unfolding,[],[f28,f54,f38,f54,f54])).
% 0.12/0.37  fof(f54,plain,(
% 0.12/0.37    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.12/0.37    inference(definition_unfolding,[],[f31,f53])).
% 0.12/0.37  fof(f53,plain,(
% 0.12/0.37    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.12/0.37    inference(definition_unfolding,[],[f34,f52])).
% 0.12/0.37  fof(f34,plain,(
% 0.12/0.37    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f12])).
% 0.12/0.37  fof(f12,axiom,(
% 0.12/0.37    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.12/0.37  fof(f31,plain,(
% 0.12/0.37    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.12/0.37    inference(cnf_transformation,[],[f11])).
% 0.12/0.37  fof(f11,axiom,(
% 0.12/0.37    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.12/0.37  fof(f28,plain,(
% 0.12/0.37    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.12/0.37    inference(cnf_transformation,[],[f21])).
% 0.12/0.37  fof(f59,plain,(
% 0.12/0.37    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k4_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 0.12/0.37    inference(definition_unfolding,[],[f36,f53,f35,f54,f54])).
% 0.12/0.37  fof(f35,plain,(
% 0.12/0.37    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.12/0.37    inference(cnf_transformation,[],[f7])).
% 0.12/0.37  fof(f7,axiom,(
% 0.12/0.37    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.12/0.37  fof(f36,plain,(
% 0.12/0.37    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.12/0.37    inference(cnf_transformation,[],[f10])).
% 0.12/0.37  fof(f10,axiom,(
% 0.12/0.37    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.12/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.12/0.37  fof(f77,plain,(
% 0.12/0.37    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 0.12/0.37    inference(equality_resolution,[],[f70])).
% 0.12/0.37  fof(f70,plain,(
% 0.12/0.37    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.12/0.37    inference(definition_unfolding,[],[f44,f52])).
% 0.12/0.37  fof(f44,plain,(
% 0.12/0.37    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.12/0.37    inference(cnf_transformation,[],[f27])).
% 0.12/0.37  % SZS output end Proof for theBenchmark
% 0.12/0.37  % (18638)------------------------------
% 0.12/0.37  % (18638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.37  % (18638)Termination reason: Refutation
% 0.12/0.37  
% 0.12/0.37  % (18638)Memory used [KB]: 10874
% 0.12/0.37  % (18638)Time elapsed: 0.071 s
% 0.12/0.37  % (18638)------------------------------
% 0.12/0.37  % (18638)------------------------------
% 0.12/0.37  % (18646)------------------------------
% 0.12/0.37  % (18646)------------------------------
% 0.12/0.37  % (18635)Refutation not found, incomplete strategy% (18635)------------------------------
% 0.12/0.37  % (18635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.37  % (18635)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.37  
% 0.12/0.37  % (18635)Memory used [KB]: 1663
% 0.12/0.37  % (18635)Time elapsed: 0.065 s
% 0.12/0.37  % (18635)------------------------------
% 0.12/0.37  % (18635)------------------------------
% 0.12/0.37  % (18659)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.12/0.37  % (18644)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.12/0.38  % (18645)Refutation not found, incomplete strategy% (18645)------------------------------
% 0.12/0.38  % (18645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.38  % (18645)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.38  
% 0.12/0.38  % (18645)Memory used [KB]: 10618
% 0.12/0.38  % (18645)Time elapsed: 0.088 s
% 0.12/0.38  % (18645)------------------------------
% 0.12/0.38  % (18645)------------------------------
% 0.12/0.38  % (18650)Refutation not found, incomplete strategy% (18650)------------------------------
% 0.12/0.38  % (18650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.38  % (18650)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.38  
% 0.12/0.38  % (18650)Memory used [KB]: 6140
% 0.12/0.38  % (18650)Time elapsed: 0.062 s
% 0.12/0.38  % (18650)------------------------------
% 0.12/0.38  % (18650)------------------------------
% 0.12/0.38  % (18634)Success in time 0.118 s
%------------------------------------------------------------------------------
