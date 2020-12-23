%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:02 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 196 expanded)
%              Number of leaves         :    8 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 346 expanded)
%              Number of equality atoms :   60 ( 252 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f73,f74])).

fof(f74,plain,(
    sK0 = sK1 ),
    inference(backward_demodulation,[],[f64,f65])).

fof(f65,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f63,f53])).

fof(f53,plain,(
    ! [X4,X2,X0] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X4,X2)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X4,X2) != X3 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X1 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f63,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
      | sK2 = X4 ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK1))
      | sK2 = X4
      | sK2 = X4
      | sK2 = X4 ) ),
    inference(resolution,[],[f58,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f30,f34])).

% (2849)Refutation not found, incomplete strategy% (2849)------------------------------
% (2849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2849)Termination reason: Refutation not found, incomplete strategy

% (2849)Memory used [KB]: 6268
% (2849)Time elapsed: 0.055 s
% (2849)------------------------------
% (2849)------------------------------
fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2))
      | ~ r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ) ),
    inference(superposition,[],[f48,f57])).

fof(f57,plain,(
    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f38,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f38,plain,(
    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f13,f35,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f15,f35])).

fof(f15,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f16,f34])).

fof(f16,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f13,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f64,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] : r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X4) != X3 ) ),
    inference(equality_resolution,[],[f39])).

% (2836)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X2 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f73,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f37,f64])).

fof(f37,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f14,f35,f36])).

fof(f14,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.07  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n016.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 17:40:49 EST 2020
% 0.11/0.26  % CPUTime    : 
% 0.11/0.34  % (2835)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.11/0.35  % (2834)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.11/0.36  % (2837)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.11/0.36  % (2855)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.11/0.36  % (2844)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.11/0.36  % (2844)Refutation not found, incomplete strategy% (2844)------------------------------
% 0.11/0.36  % (2844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.36  % (2844)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.36  
% 0.11/0.36  % (2844)Memory used [KB]: 10618
% 0.11/0.36  % (2844)Time elapsed: 0.067 s
% 0.11/0.36  % (2844)------------------------------
% 0.11/0.36  % (2844)------------------------------
% 0.11/0.36  % (2857)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.11/0.36  % (2845)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.11/0.37  % (2846)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.11/0.37  % (2845)Refutation not found, incomplete strategy% (2845)------------------------------
% 0.11/0.37  % (2845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.37  % (2845)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.37  
% 0.11/0.37  % (2845)Memory used [KB]: 10618
% 0.11/0.37  % (2845)Time elapsed: 0.067 s
% 0.11/0.37  % (2845)------------------------------
% 0.11/0.37  % (2845)------------------------------
% 0.11/0.37  % (2847)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.11/0.37  % (2848)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.11/0.37  % (2855)Refutation found. Thanks to Tanya!
% 0.11/0.37  % SZS status Theorem for theBenchmark
% 0.11/0.37  % (2849)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.11/0.37  % SZS output start Proof for theBenchmark
% 0.11/0.37  fof(f84,plain,(
% 0.11/0.37    $false),
% 0.11/0.37    inference(trivial_inequality_removal,[],[f83])).
% 0.11/0.37  fof(f83,plain,(
% 0.11/0.37    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.11/0.37    inference(forward_demodulation,[],[f73,f74])).
% 0.11/0.37  fof(f74,plain,(
% 0.11/0.37    sK0 = sK1),
% 0.11/0.37    inference(backward_demodulation,[],[f64,f65])).
% 0.11/0.37  fof(f65,plain,(
% 0.11/0.37    sK0 = sK2),
% 0.11/0.37    inference(resolution,[],[f63,f53])).
% 0.11/0.37  fof(f53,plain,(
% 0.11/0.37    ( ! [X4,X2,X0] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X4,X2))) )),
% 0.11/0.37    inference(equality_resolution,[],[f52])).
% 0.11/0.37  fof(f52,plain,(
% 0.11/0.37    ( ! [X4,X2,X0,X3] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X4,X2) != X3) )),
% 0.11/0.37    inference(equality_resolution,[],[f40])).
% 0.11/0.37  fof(f40,plain,(
% 0.11/0.37    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.11/0.37    inference(definition_unfolding,[],[f32,f34])).
% 0.11/0.37  fof(f34,plain,(
% 0.11/0.37    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.11/0.37    inference(definition_unfolding,[],[f18,f25])).
% 0.11/0.37  fof(f25,plain,(
% 0.11/0.37    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f7])).
% 0.11/0.37  fof(f7,axiom,(
% 0.11/0.37    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.11/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.11/0.37  fof(f18,plain,(
% 0.11/0.37    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f6])).
% 0.11/0.37  fof(f6,axiom,(
% 0.11/0.37    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.11/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.11/0.37  fof(f32,plain,(
% 0.11/0.37    ( ! [X4,X2,X0,X3,X1] : (X1 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.11/0.37    inference(cnf_transformation,[],[f12])).
% 0.11/0.37  fof(f12,plain,(
% 0.11/0.37    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.11/0.37    inference(ennf_transformation,[],[f3])).
% 0.11/0.37  fof(f3,axiom,(
% 0.11/0.37    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.11/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.11/0.37  fof(f63,plain,(
% 0.11/0.37    ( ! [X4] : (~r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK2 = X4) )),
% 0.11/0.37    inference(duplicate_literal_removal,[],[f62])).
% 0.11/0.37  fof(f62,plain,(
% 0.11/0.37    ( ! [X4] : (~r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | sK2 = X4 | sK2 = X4 | sK2 = X4) )),
% 0.11/0.37    inference(resolution,[],[f58,f56])).
% 0.11/0.37  fof(f56,plain,(
% 0.11/0.37    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.11/0.37    inference(equality_resolution,[],[f42])).
% 0.11/0.37  fof(f42,plain,(
% 0.11/0.37    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.11/0.37    inference(definition_unfolding,[],[f30,f34])).
% 0.11/0.37  % (2849)Refutation not found, incomplete strategy% (2849)------------------------------
% 0.11/0.37  % (2849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.37  % (2849)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.37  
% 0.11/0.37  % (2849)Memory used [KB]: 6268
% 0.11/0.37  % (2849)Time elapsed: 0.055 s
% 0.11/0.37  % (2849)------------------------------
% 0.11/0.37  % (2849)------------------------------
% 0.11/0.37  fof(f30,plain,(
% 0.11/0.37    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.11/0.37    inference(cnf_transformation,[],[f12])).
% 0.11/0.37  fof(f58,plain,(
% 0.11/0.37    ( ! [X0] : (r2_hidden(X0,k3_enumset1(sK2,sK2,sK2,sK2,sK2)) | ~r2_hidden(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) )),
% 0.11/0.37    inference(superposition,[],[f48,f57])).
% 0.11/0.37  fof(f57,plain,(
% 0.11/0.37    k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.11/0.37    inference(resolution,[],[f38,f17])).
% 0.11/0.37  fof(f17,plain,(
% 0.11/0.37    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.11/0.37    inference(cnf_transformation,[],[f11])).
% 0.11/0.37  fof(f11,plain,(
% 0.11/0.37    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.11/0.37    inference(ennf_transformation,[],[f2])).
% 0.11/0.37  fof(f2,axiom,(
% 0.11/0.37    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.11/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.11/0.37  fof(f38,plain,(
% 0.11/0.37    r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2))),
% 0.11/0.37    inference(definition_unfolding,[],[f13,f35,f36])).
% 0.11/0.37  fof(f36,plain,(
% 0.11/0.37    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.11/0.37    inference(definition_unfolding,[],[f15,f35])).
% 0.11/0.37  fof(f15,plain,(
% 0.11/0.37    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f4])).
% 0.11/0.37  fof(f4,axiom,(
% 0.11/0.37    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.11/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.11/0.37  fof(f35,plain,(
% 0.11/0.37    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.11/0.37    inference(definition_unfolding,[],[f16,f34])).
% 0.11/0.37  fof(f16,plain,(
% 0.11/0.37    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.11/0.37    inference(cnf_transformation,[],[f5])).
% 0.11/0.37  fof(f5,axiom,(
% 0.11/0.37    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.11/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.11/0.37  fof(f13,plain,(
% 0.11/0.37    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.11/0.37    inference(cnf_transformation,[],[f10])).
% 0.11/0.37  fof(f10,plain,(
% 0.11/0.37    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.11/0.37    inference(ennf_transformation,[],[f9])).
% 0.11/0.37  fof(f9,negated_conjecture,(
% 0.11/0.37    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.11/0.37    inference(negated_conjecture,[],[f8])).
% 0.11/0.37  fof(f8,conjecture,(
% 0.11/0.37    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.11/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 0.11/0.37  fof(f48,plain,(
% 0.11/0.37    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~r2_hidden(X3,X0)) )),
% 0.11/0.37    inference(equality_resolution,[],[f23])).
% 0.11/0.37  fof(f23,plain,(
% 0.11/0.37    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.11/0.37    inference(cnf_transformation,[],[f1])).
% 0.11/0.37  fof(f1,axiom,(
% 0.11/0.37    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.11/0.37    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.11/0.37  fof(f64,plain,(
% 0.11/0.37    sK1 = sK2),
% 0.11/0.37    inference(resolution,[],[f63,f51])).
% 0.11/0.37  fof(f51,plain,(
% 0.11/0.37    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_enumset1(X0,X0,X0,X1,X4))) )),
% 0.11/0.37    inference(equality_resolution,[],[f50])).
% 0.11/0.37  fof(f50,plain,(
% 0.11/0.37    ( ! [X4,X0,X3,X1] : (r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X4) != X3) )),
% 0.11/0.37    inference(equality_resolution,[],[f39])).
% 0.11/0.37  % (2836)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.11/0.37  fof(f39,plain,(
% 0.11/0.37    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 0.11/0.37    inference(definition_unfolding,[],[f33,f34])).
% 0.11/0.37  fof(f33,plain,(
% 0.11/0.37    ( ! [X4,X2,X0,X3,X1] : (X2 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.11/0.37    inference(cnf_transformation,[],[f12])).
% 0.11/0.37  fof(f73,plain,(
% 0.11/0.37    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.11/0.37    inference(backward_demodulation,[],[f37,f64])).
% 0.11/0.37  fof(f37,plain,(
% 0.11/0.37    k3_enumset1(sK0,sK0,sK0,sK0,sK1) != k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 0.11/0.37    inference(definition_unfolding,[],[f14,f35,f36])).
% 0.11/0.37  fof(f14,plain,(
% 0.11/0.37    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 0.11/0.37    inference(cnf_transformation,[],[f10])).
% 0.11/0.37  % SZS output end Proof for theBenchmark
% 0.11/0.37  % (2855)------------------------------
% 0.11/0.37  % (2855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.37  % (2855)Termination reason: Refutation
% 0.11/0.37  
% 0.11/0.37  % (2855)Memory used [KB]: 1791
% 0.11/0.37  % (2855)Time elapsed: 0.075 s
% 0.11/0.37  % (2855)------------------------------
% 0.11/0.37  % (2855)------------------------------
% 0.11/0.38  % (2833)Success in time 0.108 s
%------------------------------------------------------------------------------
