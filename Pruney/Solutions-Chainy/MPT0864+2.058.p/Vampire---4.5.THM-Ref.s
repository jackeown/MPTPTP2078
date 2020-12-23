%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:39 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 652 expanded)
%              Number of leaves         :   20 ( 213 expanded)
%              Depth                    :   20
%              Number of atoms          :  139 ( 794 expanded)
%              Number of equality atoms :  102 ( 735 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(resolution,[],[f304,f92])).

fof(f92,plain,(
    ! [X4,X2,X7,X5,X3,X1] : sP4(X7,X5,X4,X3,X2,X1,X7) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X0 != X7
      | sP4(X7,X5,X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).

fof(f304,plain,(
    ~ sP4(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f226,f291])).

fof(f291,plain,(
    sK0 = sK1 ),
    inference(unit_resulting_resolution,[],[f87,f279])).

fof(f279,plain,
    ( ~ sP4(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f277,f99])).

fof(f99,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f98,f97])).

fof(f97,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f26,f96])).

fof(f96,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f36,f27])).

fof(f27,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f36,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f26,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f37,f27])).

fof(f37,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f19])).

fof(f277,plain,(
    ~ sP4(sK2,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f270,f27])).

fof(f270,plain,(
    ! [X0] : ~ sP4(sK2,k4_tarski(X0,sK2),sK0,sK0,sK0,sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f221,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))
      | ~ sP4(X7,X5,X4,X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP4(X7,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X7,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP4(X7,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X7,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f221,plain,(
    ! [X1] : ~ r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X1,sK2))) ),
    inference(superposition,[],[f110,f179])).

fof(f179,plain,(
    ! [X0] : k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X0,sK2)) ),
    inference(superposition,[],[f78,f27])).

fof(f78,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f46,f66,f70,f66])).

fof(f70,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f66])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f47,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f48,f62])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

% (26675)Refutation not found, incomplete strategy% (26675)------------------------------
% (26675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26675)Termination reason: Refutation not found, incomplete strategy

% (26675)Memory used [KB]: 10618
% (26675)Time elapsed: 0.178 s
% (26675)------------------------------
% (26675)------------------------------
fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f110,plain,(
    ! [X2,X3] : ~ r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(global_subsumption,[],[f95,f107])).

fof(f107,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
      | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ) ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f70])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f94,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f72,f73])).

fof(f73,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f31,f67,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f66])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f66])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) ),
    inference(definition_unfolding,[],[f30,f68,f69])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f67])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f94,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f84,f71])).

fof(f71,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f29,f67])).

% (26666)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f84,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f43,f70,f68,f70,f70])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f87,plain,(
    ! [X4,X2,X0,X7,X3,X1] : sP4(X7,X7,X4,X3,X2,X1,X0) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X5 != X7
      | sP4(X7,X5,X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f226,plain,(
    ~ sP4(sK1,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f225,f86])).

fof(f225,plain,(
    ~ r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f222,f27])).

fof(f222,plain,(
    ~ r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(sK1,sK2))) ),
    inference(superposition,[],[f109,f179])).

fof(f109,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) ),
    inference(global_subsumption,[],[f95,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))
      | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(resolution,[],[f75,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (26665)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.53  % (26682)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.33/0.53  % (26674)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.54  % (26660)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.33/0.54  % (26668)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.54  % (26668)Refutation not found, incomplete strategy% (26668)------------------------------
% 1.33/0.54  % (26668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (26668)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (26668)Memory used [KB]: 10618
% 1.33/0.54  % (26668)Time elapsed: 0.131 s
% 1.33/0.54  % (26668)------------------------------
% 1.33/0.54  % (26668)------------------------------
% 1.47/0.55  % (26667)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.47/0.55  % (26667)Refutation not found, incomplete strategy% (26667)------------------------------
% 1.47/0.55  % (26667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (26667)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (26667)Memory used [KB]: 10618
% 1.47/0.55  % (26667)Time elapsed: 0.143 s
% 1.47/0.55  % (26667)------------------------------
% 1.47/0.55  % (26667)------------------------------
% 1.47/0.55  % (26684)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.55  % (26676)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.55  % (26659)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.47/0.56  % (26661)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.47/0.56  % (26675)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.56  % (26662)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.47/0.56  % (26683)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.56  % (26680)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.47/0.56  % (26662)Refutation not found, incomplete strategy% (26662)------------------------------
% 1.47/0.56  % (26662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (26662)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (26662)Memory used [KB]: 6268
% 1.47/0.56  % (26662)Time elapsed: 0.143 s
% 1.47/0.56  % (26662)------------------------------
% 1.47/0.56  % (26662)------------------------------
% 1.47/0.57  % (26672)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.47/0.57  % (26686)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.47/0.57  % (26658)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.57  % (26658)Refutation not found, incomplete strategy% (26658)------------------------------
% 1.47/0.57  % (26658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (26658)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (26658)Memory used [KB]: 1663
% 1.47/0.57  % (26658)Time elapsed: 0.152 s
% 1.47/0.57  % (26658)------------------------------
% 1.47/0.57  % (26658)------------------------------
% 1.47/0.57  % (26685)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.47/0.57  % (26663)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.47/0.57  % (26664)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.57  % (26678)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.58  % (26677)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.58  % (26670)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.58  % (26682)Refutation found. Thanks to Tanya!
% 1.47/0.58  % SZS status Theorem for theBenchmark
% 1.47/0.58  % SZS output start Proof for theBenchmark
% 1.47/0.58  fof(f325,plain,(
% 1.47/0.58    $false),
% 1.47/0.58    inference(resolution,[],[f304,f92])).
% 1.47/0.58  fof(f92,plain,(
% 1.47/0.58    ( ! [X4,X2,X7,X5,X3,X1] : (sP4(X7,X5,X4,X3,X2,X1,X7)) )),
% 1.47/0.58    inference(equality_resolution,[],[f51])).
% 1.47/0.58  fof(f51,plain,(
% 1.47/0.58    ( ! [X4,X2,X0,X7,X5,X3,X1] : (X0 != X7 | sP4(X7,X5,X4,X3,X2,X1,X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f25])).
% 1.47/0.58  fof(f25,plain,(
% 1.47/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 1.47/0.58    inference(ennf_transformation,[],[f17])).
% 1.47/0.58  fof(f17,axiom,(
% 1.47/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_enumset1)).
% 1.47/0.58  fof(f304,plain,(
% 1.47/0.58    ~sP4(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.47/0.58    inference(backward_demodulation,[],[f226,f291])).
% 1.47/0.58  fof(f291,plain,(
% 1.47/0.58    sK0 = sK1),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f87,f279])).
% 1.47/0.58  fof(f279,plain,(
% 1.47/0.58    ~sP4(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK0 = sK1),
% 1.47/0.58    inference(superposition,[],[f277,f99])).
% 1.47/0.58  fof(f99,plain,(
% 1.47/0.58    sK0 = sK2 | sK0 = sK1),
% 1.47/0.58    inference(superposition,[],[f98,f97])).
% 1.47/0.58  fof(f97,plain,(
% 1.47/0.58    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 1.47/0.58    inference(backward_demodulation,[],[f26,f96])).
% 1.47/0.58  fof(f96,plain,(
% 1.47/0.58    sK1 = k1_mcart_1(sK0)),
% 1.47/0.58    inference(superposition,[],[f36,f27])).
% 1.47/0.58  fof(f27,plain,(
% 1.47/0.58    sK0 = k4_tarski(sK1,sK2)),
% 1.47/0.58    inference(cnf_transformation,[],[f23])).
% 1.47/0.58  fof(f23,plain,(
% 1.47/0.58    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 1.47/0.58    inference(ennf_transformation,[],[f21])).
% 1.47/0.58  fof(f21,negated_conjecture,(
% 1.47/0.58    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.47/0.58    inference(negated_conjecture,[],[f20])).
% 1.47/0.58  fof(f20,conjecture,(
% 1.47/0.58    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 1.47/0.58  fof(f36,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f19])).
% 1.47/0.58  fof(f19,axiom,(
% 1.47/0.58    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.47/0.58  fof(f26,plain,(
% 1.47/0.58    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 1.47/0.58    inference(cnf_transformation,[],[f23])).
% 1.47/0.58  fof(f98,plain,(
% 1.47/0.58    sK2 = k2_mcart_1(sK0)),
% 1.47/0.58    inference(superposition,[],[f37,f27])).
% 1.47/0.58  fof(f37,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.47/0.58    inference(cnf_transformation,[],[f19])).
% 1.47/0.58  fof(f277,plain,(
% 1.47/0.58    ~sP4(sK2,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.47/0.58    inference(superposition,[],[f270,f27])).
% 1.47/0.58  fof(f270,plain,(
% 1.47/0.58    ( ! [X0] : (~sP4(sK2,k4_tarski(X0,sK2),sK0,sK0,sK0,sK0,sK0)) )),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f221,f86])).
% 1.47/0.58  fof(f86,plain,(
% 1.47/0.58    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) | ~sP4(X7,X5,X4,X3,X2,X1,X0)) )),
% 1.47/0.58    inference(equality_resolution,[],[f83])).
% 1.47/0.58  fof(f83,plain,(
% 1.47/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~sP4(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 1.47/0.58    inference(definition_unfolding,[],[f58,f62])).
% 1.47/0.58  fof(f62,plain,(
% 1.47/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f49,f50])).
% 1.47/0.58  fof(f50,plain,(
% 1.47/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f11])).
% 1.47/0.58  fof(f11,axiom,(
% 1.47/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.47/0.58  fof(f49,plain,(
% 1.47/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f10])).
% 1.47/0.58  fof(f10,axiom,(
% 1.47/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.47/0.58  fof(f58,plain,(
% 1.47/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~sP4(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.47/0.58    inference(cnf_transformation,[],[f25])).
% 1.47/0.58  fof(f221,plain,(
% 1.47/0.58    ( ! [X1] : (~r2_hidden(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X1,sK2)))) )),
% 1.47/0.58    inference(superposition,[],[f110,f179])).
% 1.47/0.58  fof(f179,plain,(
% 1.47/0.58    ( ! [X0] : (k2_zfmisc_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(X0,sK2))) )),
% 1.47/0.58    inference(superposition,[],[f78,f27])).
% 1.47/0.58  fof(f78,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f46,f66,f70,f66])).
% 1.47/0.58  fof(f70,plain,(
% 1.47/0.58    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f28,f66])).
% 1.47/0.58  fof(f28,plain,(
% 1.47/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f5])).
% 1.47/0.58  fof(f5,axiom,(
% 1.47/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.58  fof(f66,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f34,f65])).
% 1.47/0.58  fof(f65,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f44,f64])).
% 1.47/0.58  fof(f64,plain,(
% 1.47/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f47,f63])).
% 1.47/0.58  fof(f63,plain,(
% 1.47/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f48,f62])).
% 1.47/0.58  fof(f48,plain,(
% 1.47/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f9])).
% 1.47/0.58  fof(f9,axiom,(
% 1.47/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.47/0.58  % (26675)Refutation not found, incomplete strategy% (26675)------------------------------
% 1.47/0.58  % (26675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (26675)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (26675)Memory used [KB]: 10618
% 1.47/0.58  % (26675)Time elapsed: 0.178 s
% 1.47/0.58  % (26675)------------------------------
% 1.47/0.58  % (26675)------------------------------
% 1.47/0.58  fof(f47,plain,(
% 1.47/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f8])).
% 1.47/0.58  fof(f8,axiom,(
% 1.47/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.47/0.58  fof(f44,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f7])).
% 1.47/0.58  fof(f7,axiom,(
% 1.47/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.47/0.58  fof(f34,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f6])).
% 1.47/0.58  fof(f6,axiom,(
% 1.47/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.47/0.58  fof(f46,plain,(
% 1.47/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f16])).
% 1.47/0.58  fof(f16,axiom,(
% 1.47/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.47/0.58  fof(f110,plain,(
% 1.47/0.58    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))) )),
% 1.47/0.58    inference(global_subsumption,[],[f95,f107])).
% 1.47/0.58  fof(f107,plain,(
% 1.47/0.58    ( ! [X2,X3] : (~r2_hidden(X2,k2_zfmisc_1(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) )),
% 1.47/0.58    inference(resolution,[],[f75,f39])).
% 1.47/0.58  fof(f39,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f24])).
% 1.47/0.58  fof(f24,plain,(
% 1.47/0.58    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 1.47/0.58    inference(ennf_transformation,[],[f14])).
% 1.47/0.58  fof(f14,axiom,(
% 1.47/0.58    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 1.47/0.58  fof(f75,plain,(
% 1.47/0.58    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.47/0.58    inference(definition_unfolding,[],[f40,f70])).
% 1.47/0.58  fof(f40,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f12])).
% 1.47/0.58  fof(f12,axiom,(
% 1.47/0.58    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.47/0.58  fof(f95,plain,(
% 1.47/0.58    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 1.47/0.58    inference(forward_demodulation,[],[f94,f93])).
% 1.47/0.58  fof(f93,plain,(
% 1.47/0.58    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.47/0.58    inference(backward_demodulation,[],[f72,f73])).
% 1.47/0.58  fof(f73,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0) )),
% 1.47/0.58    inference(definition_unfolding,[],[f31,f67,f69])).
% 1.47/0.58  fof(f69,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f32,f66])).
% 1.47/0.58  fof(f32,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f13])).
% 1.47/0.58  fof(f13,axiom,(
% 1.47/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.47/0.58  fof(f67,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f33,f66])).
% 1.47/0.58  fof(f33,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f18])).
% 1.47/0.58  fof(f18,axiom,(
% 1.47/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.47/0.58  fof(f31,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f3])).
% 1.47/0.58  fof(f3,axiom,(
% 1.47/0.58    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.47/0.58  fof(f72,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f30,f68,f69])).
% 1.47/0.58  fof(f68,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f35,f67])).
% 1.47/0.58  fof(f35,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f2])).
% 1.47/0.58  fof(f2,axiom,(
% 1.47/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.47/0.58  fof(f30,plain,(
% 1.47/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f4])).
% 1.47/0.58  fof(f4,axiom,(
% 1.47/0.58    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.47/0.58  fof(f94,plain,(
% 1.47/0.58    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 1.47/0.58    inference(forward_demodulation,[],[f84,f71])).
% 1.47/0.58  fof(f71,plain,(
% 1.47/0.58    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.47/0.58    inference(definition_unfolding,[],[f29,f67])).
% 1.47/0.58  % (26666)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.47/0.58  fof(f29,plain,(
% 1.47/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f22])).
% 1.47/0.58  fof(f22,plain,(
% 1.47/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.47/0.58    inference(rectify,[],[f1])).
% 1.47/0.58  fof(f1,axiom,(
% 1.47/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.47/0.58  fof(f84,plain,(
% 1.47/0.58    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.47/0.58    inference(equality_resolution,[],[f76])).
% 1.47/0.58  fof(f76,plain,(
% 1.47/0.58    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 1.47/0.58    inference(definition_unfolding,[],[f43,f70,f68,f70,f70])).
% 1.47/0.58  fof(f43,plain,(
% 1.47/0.58    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.47/0.58    inference(cnf_transformation,[],[f15])).
% 1.47/0.58  fof(f15,axiom,(
% 1.47/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.47/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.47/0.58  fof(f87,plain,(
% 1.47/0.58    ( ! [X4,X2,X0,X7,X3,X1] : (sP4(X7,X7,X4,X3,X2,X1,X0)) )),
% 1.47/0.58    inference(equality_resolution,[],[f56])).
% 1.47/0.58  fof(f56,plain,(
% 1.47/0.58    ( ! [X4,X2,X0,X7,X5,X3,X1] : (X5 != X7 | sP4(X7,X5,X4,X3,X2,X1,X0)) )),
% 1.47/0.58    inference(cnf_transformation,[],[f25])).
% 1.47/0.58  fof(f226,plain,(
% 1.47/0.58    ~sP4(sK1,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.47/0.58    inference(unit_resulting_resolution,[],[f225,f86])).
% 1.47/0.58  fof(f225,plain,(
% 1.47/0.58    ~r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.47/0.58    inference(forward_demodulation,[],[f222,f27])).
% 1.47/0.58  fof(f222,plain,(
% 1.47/0.58    ~r2_hidden(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k4_tarski(sK1,sK2)))),
% 1.47/0.58    inference(superposition,[],[f109,f179])).
% 1.47/0.58  fof(f109,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))) )),
% 1.47/0.58    inference(global_subsumption,[],[f95,f106])).
% 1.47/0.58  fof(f106,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) | k1_xboole_0 = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.47/0.58    inference(resolution,[],[f75,f38])).
% 1.47/0.58  fof(f38,plain,(
% 1.47/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 1.47/0.58    inference(cnf_transformation,[],[f24])).
% 1.47/0.58  % SZS output end Proof for theBenchmark
% 1.47/0.58  % (26682)------------------------------
% 1.47/0.58  % (26682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (26682)Termination reason: Refutation
% 1.47/0.58  
% 1.47/0.58  % (26682)Memory used [KB]: 6780
% 1.47/0.58  % (26682)Time elapsed: 0.172 s
% 1.47/0.58  % (26682)------------------------------
% 1.47/0.58  % (26682)------------------------------
% 1.47/0.59  % (26657)Success in time 0.225 s
%------------------------------------------------------------------------------
