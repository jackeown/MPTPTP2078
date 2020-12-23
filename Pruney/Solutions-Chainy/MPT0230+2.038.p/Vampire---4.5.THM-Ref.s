%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:39 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 115 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :   17
%              Number of atoms          :  206 ( 384 expanded)
%              Number of equality atoms :  142 ( 262 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1238,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1237,f38])).

fof(f38,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f28])).

% (12130)Termination reason: Refutation not found, incomplete strategy

% (12130)Memory used [KB]: 10746
% (12130)Time elapsed: 0.154 s
% (12130)------------------------------
% (12130)------------------------------
fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f1237,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f1234,f37])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f1234,plain,
    ( sK1 = sK2
    | sK1 = sK3 ),
    inference(resolution,[],[f1230,f908])).

fof(f908,plain,(
    r2_hidden(sK1,k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f102,f903])).

fof(f903,plain,(
    k2_tarski(sK2,sK3) = k1_enumset1(sK2,sK3,sK1) ),
    inference(superposition,[],[f901,f152])).

fof(f152,plain,(
    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f150,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f150,plain,(
    k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK1)) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[],[f46,f148])).

fof(f148,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f145,f138])).

fof(f138,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f116,f137])).

fof(f137,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f131,f77])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f44,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f41,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f131,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f48,f122])).

fof(f122,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f120,f39])).

fof(f120,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0) ),
    inference(superposition,[],[f47,f77])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f116,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f47,f42])).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f145,plain,(
    k4_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(superposition,[],[f47,f98])).

fof(f98,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f901,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f899,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f899,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f52,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f102,plain,(
    ! [X6,X8,X7] : r2_hidden(X6,k1_enumset1(X7,X8,X6)) ),
    inference(resolution,[],[f69,f66])).

fof(f66,plain,(
    ! [X2,X5,X3,X1] :
      ( ~ sP0(X5,X1,X2,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f69,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f25,f26])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f1230,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X5,k2_tarski(X4,X6))
      | X4 = X5
      | X5 = X6 ) ),
    inference(duplicate_literal_removal,[],[f1226])).

fof(f1226,plain,(
    ! [X6,X4,X5] :
      ( X4 = X5
      | X4 = X5
      | ~ r2_hidden(X5,k2_tarski(X4,X6))
      | X5 = X6 ) ),
    inference(resolution,[],[f53,f103])).

fof(f103,plain,(
    ! [X0,X1] : sP0(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f69,f45])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:31:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.25/0.54  % (12133)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.25/0.54  % (12134)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.54  % (12133)Refutation not found, incomplete strategy% (12133)------------------------------
% 1.25/0.54  % (12133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (12133)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (12133)Memory used [KB]: 1791
% 1.25/0.54  % (12133)Time elapsed: 0.114 s
% 1.25/0.54  % (12133)------------------------------
% 1.25/0.54  % (12133)------------------------------
% 1.36/0.54  % (12139)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.54  % (12112)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  % (12125)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.54  % (12117)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.55  % (12125)Refutation not found, incomplete strategy% (12125)------------------------------
% 1.36/0.55  % (12125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (12121)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.55  % (12118)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (12125)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (12125)Memory used [KB]: 6268
% 1.36/0.55  % (12125)Time elapsed: 0.127 s
% 1.36/0.55  % (12125)------------------------------
% 1.36/0.55  % (12125)------------------------------
% 1.36/0.55  % (12132)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.56  % (12137)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.56  % (12115)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.56  % (12114)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.56  % (12110)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.56  % (12120)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.56  % (12110)Refutation not found, incomplete strategy% (12110)------------------------------
% 1.36/0.56  % (12110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (12110)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (12110)Memory used [KB]: 1663
% 1.36/0.56  % (12110)Time elapsed: 0.134 s
% 1.36/0.56  % (12110)------------------------------
% 1.36/0.56  % (12110)------------------------------
% 1.36/0.56  % (12127)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.56  % (12129)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.56  % (12126)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.56  % (12127)Refutation not found, incomplete strategy% (12127)------------------------------
% 1.36/0.56  % (12127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (12127)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (12127)Memory used [KB]: 10618
% 1.36/0.56  % (12127)Time elapsed: 0.102 s
% 1.36/0.56  % (12127)------------------------------
% 1.36/0.56  % (12127)------------------------------
% 1.36/0.56  % (12123)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.56  % (12138)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.57  % (12116)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.36/0.57  % (12124)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.57  % (12113)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.57  % (12130)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.57  % (12130)Refutation not found, incomplete strategy% (12130)------------------------------
% 1.36/0.57  % (12130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (12131)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.57  % (12128)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.57  % (12122)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.57  % (12121)Refutation not found, incomplete strategy% (12121)------------------------------
% 1.36/0.57  % (12121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (12121)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (12121)Memory used [KB]: 10618
% 1.36/0.57  % (12121)Time elapsed: 0.150 s
% 1.36/0.57  % (12121)------------------------------
% 1.36/0.57  % (12121)------------------------------
% 1.36/0.57  % (12119)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.58  % (12117)Refutation found. Thanks to Tanya!
% 1.36/0.58  % SZS status Theorem for theBenchmark
% 1.36/0.58  % (12136)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.58  % (12135)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.36/0.58  % (12120)Refutation not found, incomplete strategy% (12120)------------------------------
% 1.36/0.58  % (12120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.58  % (12120)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.58  
% 1.36/0.58  % (12120)Memory used [KB]: 10618
% 1.36/0.58  % (12120)Time elapsed: 0.159 s
% 1.36/0.58  % (12120)------------------------------
% 1.36/0.58  % (12120)------------------------------
% 1.36/0.58  % (12111)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.58  % (12119)Refutation not found, incomplete strategy% (12119)------------------------------
% 1.36/0.58  % (12119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.58  % (12119)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.58  
% 1.36/0.58  % (12119)Memory used [KB]: 10618
% 1.36/0.58  % (12119)Time elapsed: 0.130 s
% 1.36/0.58  % (12119)------------------------------
% 1.36/0.58  % (12119)------------------------------
% 1.36/0.58  % SZS output start Proof for theBenchmark
% 1.36/0.58  fof(f1238,plain,(
% 1.36/0.58    $false),
% 1.36/0.58    inference(subsumption_resolution,[],[f1237,f38])).
% 1.36/0.58  fof(f38,plain,(
% 1.36/0.58    sK1 != sK3),
% 1.36/0.58    inference(cnf_transformation,[],[f29])).
% 1.36/0.58  fof(f29,plain,(
% 1.36/0.58    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.36/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f22,f28])).
% 1.36/0.59  % (12130)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.59  
% 1.36/0.59  % (12130)Memory used [KB]: 10746
% 1.36/0.59  % (12130)Time elapsed: 0.154 s
% 1.36/0.59  % (12130)------------------------------
% 1.36/0.59  % (12130)------------------------------
% 1.36/0.59  fof(f28,plain,(
% 1.36/0.59    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 1.36/0.59    introduced(choice_axiom,[])).
% 1.36/0.59  fof(f22,plain,(
% 1.36/0.59    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.36/0.59    inference(ennf_transformation,[],[f20])).
% 1.36/0.59  fof(f20,negated_conjecture,(
% 1.36/0.59    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.36/0.59    inference(negated_conjecture,[],[f19])).
% 1.36/0.59  fof(f19,conjecture,(
% 1.36/0.59    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.36/0.59  fof(f1237,plain,(
% 1.36/0.59    sK1 = sK3),
% 1.36/0.59    inference(subsumption_resolution,[],[f1234,f37])).
% 1.36/0.59  fof(f37,plain,(
% 1.36/0.59    sK1 != sK2),
% 1.36/0.59    inference(cnf_transformation,[],[f29])).
% 1.36/0.59  fof(f1234,plain,(
% 1.36/0.59    sK1 = sK2 | sK1 = sK3),
% 1.36/0.59    inference(resolution,[],[f1230,f908])).
% 1.36/0.59  fof(f908,plain,(
% 1.36/0.59    r2_hidden(sK1,k2_tarski(sK2,sK3))),
% 1.36/0.59    inference(superposition,[],[f102,f903])).
% 1.36/0.59  fof(f903,plain,(
% 1.36/0.59    k2_tarski(sK2,sK3) = k1_enumset1(sK2,sK3,sK1)),
% 1.36/0.59    inference(superposition,[],[f901,f152])).
% 1.36/0.59  fof(f152,plain,(
% 1.36/0.59    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK1))),
% 1.36/0.59    inference(forward_demodulation,[],[f150,f39])).
% 1.36/0.59  fof(f39,plain,(
% 1.36/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.59    inference(cnf_transformation,[],[f8])).
% 1.36/0.59  fof(f8,axiom,(
% 1.36/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.36/0.59  fof(f150,plain,(
% 1.36/0.59    k2_xboole_0(k2_tarski(sK2,sK3),k1_tarski(sK1)) = k5_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0)),
% 1.36/0.59    inference(superposition,[],[f46,f148])).
% 1.36/0.59  fof(f148,plain,(
% 1.36/0.59    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.36/0.59    inference(forward_demodulation,[],[f145,f138])).
% 1.36/0.59  fof(f138,plain,(
% 1.36/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.36/0.59    inference(backward_demodulation,[],[f116,f137])).
% 1.36/0.59  fof(f137,plain,(
% 1.36/0.59    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.36/0.59    inference(forward_demodulation,[],[f131,f77])).
% 1.36/0.59  fof(f77,plain,(
% 1.36/0.59    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.36/0.59    inference(superposition,[],[f44,f74])).
% 1.36/0.59  fof(f74,plain,(
% 1.36/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.36/0.59    inference(resolution,[],[f41,f43])).
% 1.36/0.59  fof(f43,plain,(
% 1.36/0.59    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f4])).
% 1.36/0.59  fof(f4,axiom,(
% 1.36/0.59    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.36/0.59  fof(f41,plain,(
% 1.36/0.59    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.36/0.59    inference(cnf_transformation,[],[f23])).
% 1.36/0.59  fof(f23,plain,(
% 1.36/0.59    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.36/0.59    inference(ennf_transformation,[],[f6])).
% 1.36/0.59  fof(f6,axiom,(
% 1.36/0.59    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.36/0.59  fof(f44,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f1])).
% 1.36/0.59  fof(f1,axiom,(
% 1.36/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.36/0.59  fof(f131,plain,(
% 1.36/0.59    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1)) )),
% 1.36/0.59    inference(superposition,[],[f48,f122])).
% 1.36/0.59  fof(f122,plain,(
% 1.36/0.59    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 1.36/0.59    inference(forward_demodulation,[],[f120,f39])).
% 1.36/0.59  fof(f120,plain,(
% 1.36/0.59    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)) )),
% 1.36/0.59    inference(superposition,[],[f47,f77])).
% 1.36/0.59  fof(f47,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f3])).
% 1.36/0.59  fof(f3,axiom,(
% 1.36/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.36/0.59  fof(f48,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f7])).
% 1.36/0.59  fof(f7,axiom,(
% 1.36/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.36/0.59  fof(f116,plain,(
% 1.36/0.59    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.36/0.59    inference(superposition,[],[f47,f42])).
% 1.36/0.59  fof(f42,plain,(
% 1.36/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.36/0.59    inference(cnf_transformation,[],[f21])).
% 1.36/0.59  fof(f21,plain,(
% 1.36/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.36/0.59    inference(rectify,[],[f2])).
% 1.36/0.59  fof(f2,axiom,(
% 1.36/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.36/0.59  fof(f145,plain,(
% 1.36/0.59    k4_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3)) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 1.36/0.59    inference(superposition,[],[f47,f98])).
% 1.36/0.59  fof(f98,plain,(
% 1.36/0.59    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.36/0.59    inference(resolution,[],[f49,f36])).
% 1.36/0.59  fof(f36,plain,(
% 1.36/0.59    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.36/0.59    inference(cnf_transformation,[],[f29])).
% 1.36/0.59  fof(f49,plain,(
% 1.36/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.36/0.59    inference(cnf_transformation,[],[f24])).
% 1.36/0.59  fof(f24,plain,(
% 1.36/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.36/0.59    inference(ennf_transformation,[],[f5])).
% 1.36/0.59  fof(f5,axiom,(
% 1.36/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.36/0.59  fof(f46,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f9])).
% 1.36/0.59  fof(f9,axiom,(
% 1.36/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.36/0.59  fof(f901,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.36/0.59    inference(forward_demodulation,[],[f899,f50])).
% 1.36/0.59  fof(f50,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f14])).
% 1.36/0.59  fof(f14,axiom,(
% 1.36/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.36/0.59  fof(f899,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 1.36/0.59    inference(superposition,[],[f52,f45])).
% 1.36/0.59  fof(f45,plain,(
% 1.36/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f13])).
% 1.36/0.59  fof(f13,axiom,(
% 1.36/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.59  fof(f52,plain,(
% 1.36/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.36/0.59    inference(cnf_transformation,[],[f11])).
% 1.36/0.59  fof(f11,axiom,(
% 1.36/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 1.36/0.59  fof(f102,plain,(
% 1.36/0.59    ( ! [X6,X8,X7] : (r2_hidden(X6,k1_enumset1(X7,X8,X6))) )),
% 1.36/0.59    inference(resolution,[],[f69,f66])).
% 1.36/0.59  fof(f66,plain,(
% 1.36/0.59    ( ! [X2,X5,X3,X1] : (~sP0(X5,X1,X2,X3) | r2_hidden(X5,X3)) )),
% 1.36/0.59    inference(equality_resolution,[],[f56])).
% 1.36/0.59  fof(f56,plain,(
% 1.36/0.59    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 1.36/0.59    inference(cnf_transformation,[],[f34])).
% 1.36/0.59  fof(f34,plain,(
% 1.36/0.59    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.36/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 1.36/0.59  fof(f33,plain,(
% 1.36/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.36/0.59    introduced(choice_axiom,[])).
% 1.36/0.59  fof(f32,plain,(
% 1.36/0.59    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 1.36/0.59    inference(rectify,[],[f31])).
% 1.36/0.59  fof(f31,plain,(
% 1.36/0.59    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.36/0.59    inference(flattening,[],[f30])).
% 1.36/0.59  fof(f30,plain,(
% 1.36/0.59    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 1.36/0.59    inference(nnf_transformation,[],[f26])).
% 1.36/0.59  fof(f26,plain,(
% 1.36/0.59    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.36/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.36/0.59  fof(f69,plain,(
% 1.36/0.59    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 1.36/0.59    inference(equality_resolution,[],[f61])).
% 1.36/0.59  fof(f61,plain,(
% 1.36/0.59    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.36/0.59    inference(cnf_transformation,[],[f35])).
% 1.36/0.59  fof(f35,plain,(
% 1.36/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.36/0.59    inference(nnf_transformation,[],[f27])).
% 1.36/0.59  fof(f27,plain,(
% 1.36/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 1.36/0.59    inference(definition_folding,[],[f25,f26])).
% 1.36/0.59  fof(f25,plain,(
% 1.36/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.36/0.59    inference(ennf_transformation,[],[f10])).
% 1.36/0.59  fof(f10,axiom,(
% 1.36/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.36/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.36/0.59  fof(f1230,plain,(
% 1.36/0.59    ( ! [X6,X4,X5] : (~r2_hidden(X5,k2_tarski(X4,X6)) | X4 = X5 | X5 = X6) )),
% 1.36/0.59    inference(duplicate_literal_removal,[],[f1226])).
% 1.36/0.59  fof(f1226,plain,(
% 1.36/0.59    ( ! [X6,X4,X5] : (X4 = X5 | X4 = X5 | ~r2_hidden(X5,k2_tarski(X4,X6)) | X5 = X6) )),
% 1.36/0.59    inference(resolution,[],[f53,f103])).
% 1.36/0.59  fof(f103,plain,(
% 1.36/0.59    ( ! [X0,X1] : (sP0(X1,X0,X0,k2_tarski(X0,X1))) )),
% 1.36/0.59    inference(superposition,[],[f69,f45])).
% 1.36/0.59  fof(f53,plain,(
% 1.36/0.59    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 1.36/0.59    inference(cnf_transformation,[],[f34])).
% 1.36/0.59  % SZS output end Proof for theBenchmark
% 1.36/0.59  % (12117)------------------------------
% 1.36/0.59  % (12117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.59  % (12117)Termination reason: Refutation
% 1.36/0.59  
% 1.36/0.59  % (12117)Memory used [KB]: 6780
% 1.36/0.59  % (12117)Time elapsed: 0.145 s
% 1.36/0.59  % (12117)------------------------------
% 1.36/0.59  % (12117)------------------------------
% 1.36/0.59  % (12109)Success in time 0.217 s
%------------------------------------------------------------------------------
