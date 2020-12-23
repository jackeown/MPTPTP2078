%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:10 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 243 expanded)
%              Number of leaves         :   10 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  122 ( 402 expanded)
%              Number of equality atoms :   62 ( 296 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f66,f122,f76])).

fof(f76,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r1_xboole_0(X4,k3_enumset1(X5,X5,X5,X6,X3))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f66,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f122,plain,(
    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f121,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f121,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f120,f118])).

fof(f118,plain,(
    sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1 ),
    inference(resolution,[],[f115,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f115,plain,
    ( sP4(sK0,sK1,sK1,sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f114,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | sP4(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP4(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f35,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP4(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f114,plain,
    ( r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | sK0 = sK1 ),
    inference(resolution,[],[f113,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f38])).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

% (9475)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f113,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK1
    | ~ r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f41,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | sK0 = sK1 ),
    inference(definition_unfolding,[],[f18,f40,f21,f40,f40])).

fof(f18,plain,
    ( sK0 = sK1
    | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f120,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(trivial_inequality_removal,[],[f119])).

fof(f119,plain,
    ( sK0 != sK0
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f42,f118])).

fof(f42,plain,
    ( sK0 != sK1
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f17,f40,f21,f40,f40])).

fof(f17,plain,
    ( sK0 != sK1
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f52,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | ~ sP4(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X4,X0,X1] : sP4(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP4(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (9476)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (9495)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.18/0.53  % (9480)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.18/0.53  % (9472)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.18/0.53  % (9486)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.18/0.53  % (9480)Refutation not found, incomplete strategy% (9480)------------------------------
% 1.18/0.53  % (9480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.54  % (9490)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.18/0.54  % (9480)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.54  
% 1.18/0.54  % (9480)Memory used [KB]: 10618
% 1.18/0.54  % (9480)Time elapsed: 0.113 s
% 1.18/0.54  % (9480)------------------------------
% 1.18/0.54  % (9480)------------------------------
% 1.18/0.54  % (9497)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.18/0.54  % (9477)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.18/0.54  % (9474)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.18/0.54  % (9484)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.18/0.54  % (9497)Refutation found. Thanks to Tanya!
% 1.18/0.54  % SZS status Theorem for theBenchmark
% 1.18/0.54  % (9474)Refutation not found, incomplete strategy% (9474)------------------------------
% 1.18/0.54  % (9474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.54  % (9474)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.54  
% 1.18/0.54  % (9474)Memory used [KB]: 10618
% 1.18/0.54  % (9474)Time elapsed: 0.124 s
% 1.18/0.54  % (9474)------------------------------
% 1.18/0.54  % (9474)------------------------------
% 1.18/0.55  % SZS output start Proof for theBenchmark
% 1.18/0.55  fof(f126,plain,(
% 1.18/0.55    $false),
% 1.18/0.55    inference(unit_resulting_resolution,[],[f66,f122,f76])).
% 1.18/0.55  fof(f76,plain,(
% 1.18/0.55    ( ! [X6,X4,X5,X3] : (~r1_xboole_0(X4,k3_enumset1(X5,X5,X5,X6,X3)) | ~r2_hidden(X3,X4)) )),
% 1.18/0.55    inference(resolution,[],[f66,f22])).
% 1.18/0.55  fof(f22,plain,(
% 1.18/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.18/0.55    inference(cnf_transformation,[],[f14])).
% 1.18/0.55  fof(f14,plain,(
% 1.18/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.18/0.55    inference(ennf_transformation,[],[f12])).
% 1.18/0.55  fof(f12,plain,(
% 1.18/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.18/0.55    inference(rectify,[],[f1])).
% 1.18/0.55  fof(f1,axiom,(
% 1.18/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.18/0.55  fof(f122,plain,(
% 1.18/0.55    r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 1.18/0.55    inference(unit_resulting_resolution,[],[f121,f45])).
% 1.18/0.55  fof(f45,plain,(
% 1.18/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)) )),
% 1.18/0.55    inference(definition_unfolding,[],[f26,f21])).
% 1.18/0.55  fof(f21,plain,(
% 1.18/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.18/0.55    inference(cnf_transformation,[],[f2])).
% 1.18/0.55  fof(f2,axiom,(
% 1.18/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.18/0.55  fof(f26,plain,(
% 1.18/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.18/0.55    inference(cnf_transformation,[],[f3])).
% 1.18/0.55  fof(f3,axiom,(
% 1.18/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.18/0.55  fof(f121,plain,(
% 1.18/0.55    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)))),
% 1.18/0.55    inference(forward_demodulation,[],[f120,f118])).
% 1.18/0.55  fof(f118,plain,(
% 1.18/0.55    sK0 = sK1),
% 1.18/0.55    inference(duplicate_literal_removal,[],[f117])).
% 1.18/0.55  fof(f117,plain,(
% 1.18/0.55    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1),
% 1.18/0.55    inference(resolution,[],[f115,f33])).
% 1.18/0.55  fof(f33,plain,(
% 1.18/0.55    ( ! [X4,X2,X0,X1] : (~sP4(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.18/0.55    inference(cnf_transformation,[],[f16])).
% 1.18/0.55  fof(f16,plain,(
% 1.18/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.18/0.55    inference(ennf_transformation,[],[f4])).
% 1.18/0.55  fof(f4,axiom,(
% 1.18/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.18/0.55  fof(f115,plain,(
% 1.18/0.55    sP4(sK0,sK1,sK1,sK1) | sK0 = sK1),
% 1.18/0.55    inference(resolution,[],[f114,f50])).
% 1.18/0.55  fof(f50,plain,(
% 1.18/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | sP4(X4,X2,X1,X0)) )),
% 1.18/0.55    inference(equality_resolution,[],[f48])).
% 1.18/0.55  fof(f48,plain,(
% 1.18/0.55    ( ! [X4,X2,X0,X3,X1] : (sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.18/0.55    inference(definition_unfolding,[],[f35,f38])).
% 1.18/0.55  fof(f38,plain,(
% 1.18/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.18/0.55    inference(definition_unfolding,[],[f28,f29])).
% 1.18/0.55  fof(f29,plain,(
% 1.18/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.18/0.55    inference(cnf_transformation,[],[f8])).
% 1.18/0.55  fof(f8,axiom,(
% 1.18/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.18/0.55  fof(f28,plain,(
% 1.18/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.18/0.55    inference(cnf_transformation,[],[f7])).
% 1.18/0.55  fof(f7,axiom,(
% 1.18/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.18/0.55  fof(f35,plain,(
% 1.18/0.55    ( ! [X4,X2,X0,X3,X1] : (sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.18/0.55    inference(cnf_transformation,[],[f16])).
% 1.18/0.55  fof(f114,plain,(
% 1.18/0.55    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | sK0 = sK1),
% 1.18/0.55    inference(resolution,[],[f113,f43])).
% 1.18/0.55  fof(f43,plain,(
% 1.18/0.55    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.18/0.55    inference(definition_unfolding,[],[f25,f40])).
% 1.18/0.55  fof(f40,plain,(
% 1.18/0.55    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.18/0.55    inference(definition_unfolding,[],[f19,f39])).
% 1.18/0.55  fof(f39,plain,(
% 1.18/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.18/0.55    inference(definition_unfolding,[],[f20,f38])).
% 1.18/0.55  fof(f20,plain,(
% 1.18/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.18/0.55    inference(cnf_transformation,[],[f6])).
% 1.18/0.55  fof(f6,axiom,(
% 1.18/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.18/0.55  % (9475)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.18/0.55  fof(f19,plain,(
% 1.18/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.18/0.55    inference(cnf_transformation,[],[f5])).
% 1.18/0.55  fof(f5,axiom,(
% 1.18/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.18/0.55  fof(f25,plain,(
% 1.18/0.55    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.18/0.55    inference(cnf_transformation,[],[f15])).
% 1.18/0.55  fof(f15,plain,(
% 1.18/0.55    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.18/0.55    inference(ennf_transformation,[],[f9])).
% 1.18/0.55  fof(f9,axiom,(
% 1.18/0.55    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.18/0.55  fof(f113,plain,(
% 1.18/0.55    ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | sK0 = sK1),
% 1.18/0.55    inference(trivial_inequality_removal,[],[f112])).
% 1.18/0.55  fof(f112,plain,(
% 1.18/0.55    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK1 | ~r1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 1.18/0.55    inference(superposition,[],[f41,f44])).
% 1.18/0.55  fof(f44,plain,(
% 1.18/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.18/0.55    inference(definition_unfolding,[],[f27,f21])).
% 1.18/0.55  fof(f27,plain,(
% 1.18/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.18/0.55    inference(cnf_transformation,[],[f3])).
% 1.18/0.55  fof(f41,plain,(
% 1.18/0.55    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | sK0 = sK1),
% 1.18/0.55    inference(definition_unfolding,[],[f18,f40,f21,f40,f40])).
% 1.18/0.55  fof(f18,plain,(
% 1.18/0.55    sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.18/0.55    inference(cnf_transformation,[],[f13])).
% 1.18/0.55  fof(f13,plain,(
% 1.18/0.55    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 1.18/0.55    inference(ennf_transformation,[],[f11])).
% 1.18/0.55  fof(f11,negated_conjecture,(
% 1.18/0.55    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.18/0.55    inference(negated_conjecture,[],[f10])).
% 1.18/0.55  fof(f10,conjecture,(
% 1.18/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.18/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.18/0.55  fof(f120,plain,(
% 1.18/0.55    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.18/0.55    inference(trivial_inequality_removal,[],[f119])).
% 1.18/0.55  fof(f119,plain,(
% 1.18/0.55    sK0 != sK0 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.18/0.55    inference(backward_demodulation,[],[f42,f118])).
% 1.18/0.55  fof(f42,plain,(
% 1.18/0.55    sK0 != sK1 | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.18/0.55    inference(definition_unfolding,[],[f17,f40,f21,f40,f40])).
% 1.18/0.55  fof(f17,plain,(
% 1.18/0.55    sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.18/0.55    inference(cnf_transformation,[],[f13])).
% 1.18/0.55  fof(f66,plain,(
% 1.18/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X0))) )),
% 1.18/0.55    inference(unit_resulting_resolution,[],[f52,f51])).
% 1.18/0.55  fof(f51,plain,(
% 1.18/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | ~sP4(X4,X2,X1,X0)) )),
% 1.18/0.55    inference(equality_resolution,[],[f49])).
% 1.18/0.55  fof(f49,plain,(
% 1.18/0.55    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 1.18/0.55    inference(definition_unfolding,[],[f34,f38])).
% 1.18/0.55  fof(f34,plain,(
% 1.18/0.55    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.18/0.55    inference(cnf_transformation,[],[f16])).
% 1.18/0.55  fof(f52,plain,(
% 1.18/0.55    ( ! [X4,X0,X1] : (sP4(X4,X4,X1,X0)) )),
% 1.18/0.55    inference(equality_resolution,[],[f32])).
% 1.18/0.55  fof(f32,plain,(
% 1.18/0.55    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP4(X4,X2,X1,X0)) )),
% 1.18/0.55    inference(cnf_transformation,[],[f16])).
% 1.18/0.55  % SZS output end Proof for theBenchmark
% 1.18/0.55  % (9497)------------------------------
% 1.18/0.55  % (9497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.55  % (9497)Termination reason: Refutation
% 1.18/0.55  
% 1.18/0.55  % (9497)Memory used [KB]: 6268
% 1.18/0.55  % (9497)Time elapsed: 0.121 s
% 1.18/0.55  % (9497)------------------------------
% 1.18/0.55  % (9497)------------------------------
% 1.44/0.55  % (9470)Success in time 0.182 s
%------------------------------------------------------------------------------
