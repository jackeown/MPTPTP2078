%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:34 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 472 expanded)
%              Number of leaves         :   20 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          :  131 ( 588 expanded)
%              Number of equality atoms :   60 ( 415 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f651,plain,(
    $false ),
    inference(subsumption_resolution,[],[f650,f80])).

fof(f80,plain,(
    sK1 != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f68,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f65,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

% (31710)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (31693)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (31693)Refutation not found, incomplete strategy% (31693)------------------------------
% (31693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31693)Termination reason: Refutation not found, incomplete strategy

% (31693)Memory used [KB]: 10618
% (31693)Time elapsed: 0.191 s
% (31693)------------------------------
% (31693)------------------------------
fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f68,plain,(
    sK1 != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f33,f66,f67])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f65])).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f65])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f650,plain,(
    sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f649,f69])).

fof(f69,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f34,f66])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f649,plain,(
    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f641,f333])).

fof(f333,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f332,f182])).

fof(f182,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f176,f86])).

fof(f86,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f48,f78])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f176,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f173,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f57,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f173,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f169,f166])).

fof(f166,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[],[f151,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f151,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X0)
      | r1_xboole_0(k1_xboole_0,k1_xboole_0) ) ),
    inference(resolution,[],[f141,f96])).

fof(f96,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0,X0),X0)
      | r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f44,f86])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f99,f125])).

fof(f125,plain,(
    ! [X0] : k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f69,f71])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f66])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f169,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f151,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2(X0,X0))
      | r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f96,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f332,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f331,f142])).

fof(f142,plain,(
    ! [X6] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f101,f125])).

fof(f101,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_tarski(k4_enumset1(X5,X5,X5,X5,X5,X6))) = X5 ),
    inference(resolution,[],[f70,f48])).

fof(f331,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f327,f86])).

fof(f327,plain,(
    ! [X3] : k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,k3_xboole_0(X3,X3)) ),
    inference(superposition,[],[f72,f125])).

fof(f72,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f41,f40,f40,f66])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f641,plain,(
    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(superposition,[],[f73,f628])).

fof(f628,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f111,f32])).

fof(f32,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,X8)
      | k4_enumset1(X7,X7,X7,X7,X7,X7) = k3_xboole_0(k4_enumset1(X7,X7,X7,X7,X7,X7),X8) ) ),
    inference(resolution,[],[f77,f48])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f67])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f73,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f42,f66,f40,f66])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:11:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (31696)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (31681)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (31698)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (31687)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (31706)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (31702)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (31691)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (31712)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (31708)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (31699)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (31692)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.65/0.57  % (31689)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.65/0.58  % (31709)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.65/0.58  % (31692)Refutation not found, incomplete strategy% (31692)------------------------------
% 1.65/0.58  % (31692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (31692)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.58  
% 1.65/0.58  % (31692)Memory used [KB]: 10618
% 1.65/0.58  % (31692)Time elapsed: 0.133 s
% 1.65/0.58  % (31692)------------------------------
% 1.65/0.58  % (31692)------------------------------
% 1.65/0.58  % (31682)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.65/0.58  % (31690)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.65/0.58  % (31686)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.65/0.58  % (31707)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.65/0.58  % (31685)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.65/0.58  % (31697)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.65/0.59  % (31690)Refutation not found, incomplete strategy% (31690)------------------------------
% 1.65/0.59  % (31690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (31690)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (31690)Memory used [KB]: 10618
% 1.65/0.59  % (31690)Time elapsed: 0.181 s
% 1.65/0.59  % (31690)------------------------------
% 1.65/0.59  % (31690)------------------------------
% 1.65/0.59  % (31700)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.65/0.59  % (31703)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.78/0.59  % (31682)Refutation not found, incomplete strategy% (31682)------------------------------
% 1.78/0.59  % (31682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (31682)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.59  
% 1.78/0.59  % (31682)Memory used [KB]: 10746
% 1.78/0.59  % (31682)Time elapsed: 0.156 s
% 1.78/0.59  % (31682)------------------------------
% 1.78/0.59  % (31682)------------------------------
% 1.78/0.59  % (31684)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.78/0.59  % (31705)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.78/0.60  % (31705)Refutation not found, incomplete strategy% (31705)------------------------------
% 1.78/0.60  % (31705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (31705)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (31705)Memory used [KB]: 10746
% 1.78/0.60  % (31705)Time elapsed: 0.165 s
% 1.78/0.60  % (31705)------------------------------
% 1.78/0.60  % (31705)------------------------------
% 1.78/0.60  % (31701)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.78/0.60  % (31687)Refutation found. Thanks to Tanya!
% 1.78/0.60  % SZS status Theorem for theBenchmark
% 1.78/0.60  % SZS output start Proof for theBenchmark
% 1.78/0.60  fof(f651,plain,(
% 1.78/0.60    $false),
% 1.78/0.60    inference(subsumption_resolution,[],[f650,f80])).
% 1.78/0.60  fof(f80,plain,(
% 1.78/0.60    sK1 != k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.78/0.60    inference(backward_demodulation,[],[f68,f71])).
% 1.78/0.60  fof(f71,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f37,f65,f65])).
% 1.78/0.60  fof(f65,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f38,f64])).
% 1.78/0.60  fof(f64,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f60,f63])).
% 1.78/0.60  fof(f63,plain,(
% 1.78/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f61,f62])).
% 1.78/0.60  fof(f62,plain,(
% 1.78/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f19])).
% 1.78/0.60  fof(f19,axiom,(
% 1.78/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.78/0.60  fof(f61,plain,(
% 1.78/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f18])).
% 1.78/0.60  fof(f18,axiom,(
% 1.78/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.78/0.60  fof(f60,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f17])).
% 1.78/0.60  fof(f17,axiom,(
% 1.78/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.78/0.60  % (31710)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.78/0.60  % (31693)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.78/0.60  % (31693)Refutation not found, incomplete strategy% (31693)------------------------------
% 1.78/0.60  % (31693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (31693)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (31693)Memory used [KB]: 10618
% 1.78/0.60  % (31693)Time elapsed: 0.191 s
% 1.78/0.60  % (31693)------------------------------
% 1.78/0.60  % (31693)------------------------------
% 1.78/0.60  fof(f38,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f16])).
% 1.78/0.60  fof(f16,axiom,(
% 1.78/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.78/0.60  fof(f37,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f14])).
% 1.78/0.60  fof(f14,axiom,(
% 1.78/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.78/0.60  fof(f68,plain,(
% 1.78/0.60    sK1 != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.78/0.60    inference(definition_unfolding,[],[f33,f66,f67])).
% 1.78/0.60  fof(f67,plain,(
% 1.78/0.60    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f35,f65])).
% 1.78/0.60  fof(f35,plain,(
% 1.78/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f15])).
% 1.78/0.60  fof(f15,axiom,(
% 1.78/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.78/0.60  fof(f66,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.78/0.60    inference(definition_unfolding,[],[f39,f65])).
% 1.78/0.60  fof(f39,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f21])).
% 1.78/0.60  fof(f21,axiom,(
% 1.78/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.78/0.60  fof(f33,plain,(
% 1.78/0.60    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.78/0.60    inference(cnf_transformation,[],[f26])).
% 1.78/0.60  fof(f26,plain,(
% 1.78/0.60    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.78/0.60    inference(ennf_transformation,[],[f23])).
% 1.78/0.60  fof(f23,negated_conjecture,(
% 1.78/0.60    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.78/0.60    inference(negated_conjecture,[],[f22])).
% 1.78/0.60  fof(f22,conjecture,(
% 1.78/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.78/0.60  fof(f650,plain,(
% 1.78/0.60    sK1 = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.78/0.60    inference(forward_demodulation,[],[f649,f69])).
% 1.78/0.60  fof(f69,plain,(
% 1.78/0.60    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.78/0.60    inference(definition_unfolding,[],[f34,f66])).
% 1.78/0.60  fof(f34,plain,(
% 1.78/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.78/0.60    inference(cnf_transformation,[],[f8])).
% 1.78/0.60  fof(f8,axiom,(
% 1.78/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.78/0.60  fof(f649,plain,(
% 1.78/0.60    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k1_xboole_0))),
% 1.78/0.60    inference(forward_demodulation,[],[f641,f333])).
% 1.78/0.60  fof(f333,plain,(
% 1.78/0.60    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 1.78/0.60    inference(forward_demodulation,[],[f332,f182])).
% 1.78/0.60  fof(f182,plain,(
% 1.78/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.78/0.60    inference(forward_demodulation,[],[f176,f86])).
% 1.78/0.60  fof(f86,plain,(
% 1.78/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.78/0.60    inference(resolution,[],[f48,f78])).
% 1.78/0.60  fof(f78,plain,(
% 1.78/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.78/0.60    inference(equality_resolution,[],[f51])).
% 1.78/0.60  fof(f51,plain,(
% 1.78/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.78/0.60    inference(cnf_transformation,[],[f6])).
% 1.78/0.60  fof(f6,axiom,(
% 1.78/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.78/0.60  fof(f48,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.78/0.60    inference(cnf_transformation,[],[f29])).
% 1.78/0.60  fof(f29,plain,(
% 1.78/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.78/0.60    inference(ennf_transformation,[],[f9])).
% 1.78/0.60  fof(f9,axiom,(
% 1.78/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.78/0.60  fof(f176,plain,(
% 1.78/0.60    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.78/0.60    inference(resolution,[],[f173,f74])).
% 1.78/0.60  fof(f74,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.78/0.60    inference(definition_unfolding,[],[f57,f40])).
% 1.78/0.60  fof(f40,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f7])).
% 1.78/0.60  fof(f7,axiom,(
% 1.78/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.78/0.60  fof(f57,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f13])).
% 1.78/0.60  fof(f13,axiom,(
% 1.78/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.78/0.60  fof(f173,plain,(
% 1.78/0.60    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f169,f166])).
% 1.78/0.60  fof(f166,plain,(
% 1.78/0.60    ( ! [X2,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.78/0.60    inference(resolution,[],[f151,f43])).
% 1.78/0.60  fof(f43,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f27])).
% 1.78/0.60  fof(f27,plain,(
% 1.78/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.78/0.60    inference(ennf_transformation,[],[f24])).
% 1.78/0.60  fof(f24,plain,(
% 1.78/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.78/0.60    inference(rectify,[],[f5])).
% 1.78/0.60  fof(f5,axiom,(
% 1.78/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.78/0.60  fof(f151,plain,(
% 1.78/0.60    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,k1_xboole_0),X0) | r1_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.78/0.60    inference(resolution,[],[f141,f96])).
% 1.78/0.60  fof(f96,plain,(
% 1.78/0.60    ( ! [X0] : (r2_hidden(sK2(X0,X0),X0) | r1_xboole_0(X0,X0)) )),
% 1.78/0.60    inference(superposition,[],[f44,f86])).
% 1.78/0.60  fof(f44,plain,(
% 1.78/0.60    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f27])).
% 1.78/0.60  fof(f141,plain,(
% 1.78/0.60    ( ! [X4,X5] : (~r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,X4)) )),
% 1.78/0.60    inference(superposition,[],[f99,f125])).
% 1.78/0.60  fof(f125,plain,(
% 1.78/0.60    ( ! [X0] : (k3_tarski(k4_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.78/0.60    inference(superposition,[],[f69,f71])).
% 1.78/0.60  fof(f99,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X2))) | ~r2_hidden(X0,X1)) )),
% 1.78/0.60    inference(resolution,[],[f70,f53])).
% 1.78/0.60  fof(f53,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f31])).
% 1.78/0.60  fof(f31,plain,(
% 1.78/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f3])).
% 1.78/0.60  fof(f3,axiom,(
% 1.78/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.78/0.60  fof(f70,plain,(
% 1.78/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.78/0.60    inference(definition_unfolding,[],[f36,f66])).
% 1.78/0.60  fof(f36,plain,(
% 1.78/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f12])).
% 1.78/0.60  fof(f12,axiom,(
% 1.78/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.78/0.60  fof(f169,plain,(
% 1.78/0.60    r1_xboole_0(k1_xboole_0,k1_xboole_0) | r1_xboole_0(sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0))),
% 1.78/0.60    inference(resolution,[],[f151,f97])).
% 1.78/0.60  fof(f97,plain,(
% 1.78/0.60    ( ! [X0] : (~r2_hidden(X0,sK2(X0,X0)) | r1_xboole_0(X0,X0)) )),
% 1.78/0.60    inference(resolution,[],[f96,f49])).
% 1.78/0.60  fof(f49,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f30])).
% 1.78/0.60  fof(f30,plain,(
% 1.78/0.60    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.78/0.60    inference(ennf_transformation,[],[f1])).
% 1.78/0.60  fof(f1,axiom,(
% 1.78/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.78/0.60  fof(f332,plain,(
% 1.78/0.60    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X3,X3)) )),
% 1.78/0.60    inference(forward_demodulation,[],[f331,f142])).
% 1.78/0.60  fof(f142,plain,(
% 1.78/0.60    ( ! [X6] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)) )),
% 1.78/0.60    inference(superposition,[],[f101,f125])).
% 1.78/0.60  fof(f101,plain,(
% 1.78/0.60    ( ! [X6,X5] : (k3_xboole_0(X5,k3_tarski(k4_enumset1(X5,X5,X5,X5,X5,X6))) = X5) )),
% 1.78/0.60    inference(resolution,[],[f70,f48])).
% 1.78/0.60  fof(f331,plain,(
% 1.78/0.60    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,X3)) )),
% 1.78/0.60    inference(forward_demodulation,[],[f327,f86])).
% 1.78/0.60  fof(f327,plain,(
% 1.78/0.60    ( ! [X3] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X3)) = k5_xboole_0(X3,k3_xboole_0(X3,X3))) )),
% 1.78/0.60    inference(superposition,[],[f72,f125])).
% 1.78/0.60  fof(f72,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X1))) )),
% 1.78/0.60    inference(definition_unfolding,[],[f41,f40,f40,f66])).
% 1.78/0.60  fof(f41,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f11])).
% 1.78/0.60  fof(f11,axiom,(
% 1.78/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.78/0.60  fof(f641,plain,(
% 1.78/0.60    k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))) = k3_tarski(k4_enumset1(sK1,sK1,sK1,sK1,sK1,k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.78/0.60    inference(superposition,[],[f73,f628])).
% 1.78/0.60  fof(f628,plain,(
% 1.78/0.60    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.78/0.60    inference(resolution,[],[f111,f32])).
% 1.78/0.60  fof(f32,plain,(
% 1.78/0.60    r2_hidden(sK0,sK1)),
% 1.78/0.60    inference(cnf_transformation,[],[f26])).
% 1.78/0.60  fof(f111,plain,(
% 1.78/0.60    ( ! [X8,X7] : (~r2_hidden(X7,X8) | k4_enumset1(X7,X7,X7,X7,X7,X7) = k3_xboole_0(k4_enumset1(X7,X7,X7,X7,X7,X7),X8)) )),
% 1.78/0.60    inference(resolution,[],[f77,f48])).
% 1.78/0.60  fof(f77,plain,(
% 1.78/0.60    ( ! [X0,X1] : (r1_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.78/0.60    inference(definition_unfolding,[],[f58,f67])).
% 1.78/0.60  fof(f58,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f20])).
% 1.78/0.60  fof(f20,axiom,(
% 1.78/0.60    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.78/0.60  fof(f73,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.78/0.60    inference(definition_unfolding,[],[f42,f66,f40,f66])).
% 1.78/0.60  fof(f42,plain,(
% 1.78/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f10])).
% 1.78/0.60  fof(f10,axiom,(
% 1.78/0.60    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.78/0.60  % SZS output end Proof for theBenchmark
% 1.78/0.60  % (31687)------------------------------
% 1.78/0.60  % (31687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (31687)Termination reason: Refutation
% 1.78/0.60  
% 1.78/0.60  % (31687)Memory used [KB]: 6652
% 1.78/0.60  % (31687)Time elapsed: 0.189 s
% 1.78/0.60  % (31687)------------------------------
% 1.78/0.60  % (31687)------------------------------
% 1.78/0.60  % (31694)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.78/0.61  % (31674)Success in time 0.24 s
%------------------------------------------------------------------------------
