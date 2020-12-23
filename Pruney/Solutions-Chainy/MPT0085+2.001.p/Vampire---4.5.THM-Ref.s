%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:21 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 133 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :   75 ( 158 expanded)
%              Number of equality atoms :   41 ( 121 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1066,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1065])).

fof(f1065,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f33,f1049])).

fof(f1049,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f32,f990])).

fof(f990,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f287,f976])).

fof(f976,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f940,f76])).

fof(f76,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f36,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f940,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f130,f136])).

fof(f136,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f127,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f127,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f32,f97])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f34,f94])).

fof(f94,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f88,f80])).

fof(f80,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(superposition,[],[f76,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f88,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X4) ),
    inference(superposition,[],[f80,f24])).

fof(f130,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X9,k4_xboole_0(X7,X8)) = k2_xboole_0(X9,k4_xboole_0(X7,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f24,f32])).

fof(f287,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f237,f21])).

fof(f237,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f236,f80])).

fof(f236,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f231,f21])).

fof(f231,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f24,f144])).

fof(f144,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f121,f76])).

fof(f121,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f109,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f109,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) ),
    inference(unit_resulting_resolution,[],[f103,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f103,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f18,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f33,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f19,f25,f25])).

fof(f19,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:22:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (16007)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (15999)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (15991)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (15996)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15997)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (15990)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (15987)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (15988)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (15984)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (15989)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (15986)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (15984)Refutation not found, incomplete strategy% (15984)------------------------------
% 0.21/0.54  % (15984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15984)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15984)Memory used [KB]: 1791
% 0.21/0.54  % (15984)Time elapsed: 0.124 s
% 0.21/0.54  % (15984)------------------------------
% 0.21/0.54  % (15984)------------------------------
% 0.21/0.54  % (15986)Refutation not found, incomplete strategy% (15986)------------------------------
% 0.21/0.54  % (15986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15986)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15986)Memory used [KB]: 10618
% 0.21/0.54  % (15986)Time elapsed: 0.125 s
% 0.21/0.54  % (15986)------------------------------
% 0.21/0.54  % (15986)------------------------------
% 1.34/0.55  % (16002)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.55  % (16006)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.55  % (16006)Refutation not found, incomplete strategy% (16006)------------------------------
% 1.34/0.55  % (16006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (16006)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (16006)Memory used [KB]: 10618
% 1.34/0.55  % (16006)Time elapsed: 0.137 s
% 1.34/0.55  % (16006)------------------------------
% 1.34/0.55  % (16006)------------------------------
% 1.34/0.55  % (16003)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.55  % (16012)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.34/0.55  % (16013)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.34/0.55  % (15994)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.34/0.55  % (15994)Refutation not found, incomplete strategy% (15994)------------------------------
% 1.34/0.55  % (15994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (15994)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (15994)Memory used [KB]: 10618
% 1.34/0.55  % (15994)Time elapsed: 0.147 s
% 1.34/0.55  % (15994)------------------------------
% 1.34/0.55  % (15994)------------------------------
% 1.34/0.55  % (15995)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.56  % (16010)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.56  % (16004)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.56  % (15995)Refutation not found, incomplete strategy% (15995)------------------------------
% 1.34/0.56  % (15995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (15995)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (15995)Memory used [KB]: 10618
% 1.34/0.56  % (15995)Time elapsed: 0.147 s
% 1.34/0.56  % (15995)------------------------------
% 1.34/0.56  % (15995)------------------------------
% 1.34/0.56  % (15998)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.56  % (16009)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.56  % (16005)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.34/0.56  % (15985)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.56  % (16011)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.59/0.57  % (16001)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.57  % (16001)Refutation not found, incomplete strategy% (16001)------------------------------
% 1.59/0.57  % (16001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (16001)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (16001)Memory used [KB]: 10618
% 1.59/0.57  % (16001)Time elapsed: 0.157 s
% 1.59/0.57  % (16001)------------------------------
% 1.59/0.57  % (16001)------------------------------
% 1.59/0.57  % (16008)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.58  % (15993)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.59/0.58  % (16000)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.58  % (15993)Refutation not found, incomplete strategy% (15993)------------------------------
% 1.59/0.58  % (15993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (15993)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (15993)Memory used [KB]: 10746
% 1.59/0.58  % (15993)Time elapsed: 0.169 s
% 1.59/0.58  % (15993)------------------------------
% 1.59/0.58  % (15993)------------------------------
% 1.59/0.58  % (15992)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.59/0.60  % (15992)Refutation not found, incomplete strategy% (15992)------------------------------
% 1.59/0.60  % (15992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.60  % (15992)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.60  
% 1.59/0.60  % (15992)Memory used [KB]: 10618
% 1.59/0.60  % (15992)Time elapsed: 0.160 s
% 1.59/0.60  % (15992)------------------------------
% 1.59/0.60  % (15992)------------------------------
% 1.96/0.63  % (16008)Refutation found. Thanks to Tanya!
% 1.96/0.63  % SZS status Theorem for theBenchmark
% 1.96/0.63  % SZS output start Proof for theBenchmark
% 1.96/0.63  fof(f1066,plain,(
% 1.96/0.63    $false),
% 1.96/0.63    inference(trivial_inequality_removal,[],[f1065])).
% 1.96/0.63  fof(f1065,plain,(
% 1.96/0.63    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.96/0.63    inference(backward_demodulation,[],[f33,f1049])).
% 1.96/0.63  fof(f1049,plain,(
% 1.96/0.63    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 1.96/0.63    inference(superposition,[],[f32,f990])).
% 1.96/0.63  fof(f990,plain,(
% 1.96/0.63    sK0 = k4_xboole_0(sK0,sK1)),
% 1.96/0.63    inference(backward_demodulation,[],[f287,f976])).
% 1.96/0.63  fof(f976,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.96/0.63    inference(forward_demodulation,[],[f940,f76])).
% 1.96/0.63  fof(f76,plain,(
% 1.96/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.96/0.63    inference(superposition,[],[f36,f34])).
% 1.96/0.63  fof(f34,plain,(
% 1.96/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.96/0.63    inference(definition_unfolding,[],[f20,f25])).
% 1.96/0.63  fof(f25,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.96/0.63    inference(cnf_transformation,[],[f10])).
% 1.96/0.63  fof(f10,axiom,(
% 1.96/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.96/0.63  fof(f20,plain,(
% 1.96/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f7])).
% 1.96/0.63  fof(f7,axiom,(
% 1.96/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.96/0.63  fof(f36,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 1.96/0.63    inference(definition_unfolding,[],[f23,f25])).
% 1.96/0.63  fof(f23,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.96/0.63    inference(cnf_transformation,[],[f6])).
% 1.96/0.63  fof(f6,axiom,(
% 1.96/0.63    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.96/0.63  fof(f940,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.96/0.63    inference(superposition,[],[f130,f136])).
% 1.96/0.63  fof(f136,plain,(
% 1.96/0.63    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 1.96/0.63    inference(forward_demodulation,[],[f127,f24])).
% 1.96/0.63  fof(f24,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.96/0.63    inference(cnf_transformation,[],[f8])).
% 1.96/0.63  fof(f8,axiom,(
% 1.96/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.96/0.63  fof(f127,plain,(
% 1.96/0.63    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4)))) )),
% 1.96/0.63    inference(superposition,[],[f32,f97])).
% 1.96/0.63  fof(f97,plain,(
% 1.96/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.96/0.63    inference(backward_demodulation,[],[f34,f94])).
% 1.96/0.63  fof(f94,plain,(
% 1.96/0.63    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 1.96/0.63    inference(forward_demodulation,[],[f88,f80])).
% 1.96/0.63  fof(f80,plain,(
% 1.96/0.63    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 1.96/0.63    inference(superposition,[],[f76,f21])).
% 1.96/0.63  fof(f21,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f1])).
% 1.96/0.63  fof(f1,axiom,(
% 1.96/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.96/0.63  fof(f88,plain,(
% 1.96/0.63    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X4)) )),
% 1.96/0.63    inference(superposition,[],[f80,f24])).
% 1.96/0.63  fof(f130,plain,(
% 1.96/0.63    ( ! [X8,X7,X9] : (k2_xboole_0(X9,k4_xboole_0(X7,X8)) = k2_xboole_0(X9,k4_xboole_0(X7,k2_xboole_0(X8,X9)))) )),
% 1.96/0.63    inference(superposition,[],[f24,f32])).
% 1.96/0.63  fof(f287,plain,(
% 1.96/0.63    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.96/0.63    inference(superposition,[],[f237,f21])).
% 1.96/0.63  fof(f237,plain,(
% 1.96/0.63    k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 1.96/0.63    inference(forward_demodulation,[],[f236,f80])).
% 1.96/0.63  fof(f236,plain,(
% 1.96/0.63    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 1.96/0.63    inference(forward_demodulation,[],[f231,f21])).
% 1.96/0.63  fof(f231,plain,(
% 1.96/0.63    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.96/0.63    inference(superposition,[],[f24,f144])).
% 1.96/0.63  fof(f144,plain,(
% 1.96/0.63    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.96/0.63    inference(superposition,[],[f121,f76])).
% 1.96/0.63  fof(f121,plain,(
% 1.96/0.63    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) = X0) )),
% 1.96/0.63    inference(unit_resulting_resolution,[],[f109,f28])).
% 1.96/0.63  fof(f28,plain,(
% 1.96/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f16])).
% 1.96/0.63  fof(f16,plain,(
% 1.96/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.96/0.63    inference(ennf_transformation,[],[f5])).
% 1.96/0.63  fof(f5,axiom,(
% 1.96/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.96/0.63  fof(f109,plain,(
% 1.96/0.63    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)) )),
% 1.96/0.63    inference(unit_resulting_resolution,[],[f103,f30])).
% 1.96/0.63  fof(f30,plain,(
% 1.96/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f17])).
% 1.96/0.63  fof(f17,plain,(
% 1.96/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.96/0.63    inference(ennf_transformation,[],[f3])).
% 1.96/0.63  fof(f3,axiom,(
% 1.96/0.63    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.96/0.63  fof(f103,plain,(
% 1.96/0.63    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) )),
% 1.96/0.63    inference(unit_resulting_resolution,[],[f18,f38])).
% 1.96/0.63  fof(f38,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.96/0.63    inference(definition_unfolding,[],[f26,f25])).
% 1.96/0.63  fof(f26,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.96/0.63    inference(cnf_transformation,[],[f15])).
% 1.96/0.63  fof(f15,plain,(
% 1.96/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.96/0.63    inference(ennf_transformation,[],[f13])).
% 1.96/0.63  fof(f13,plain,(
% 1.96/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.96/0.63    inference(rectify,[],[f4])).
% 1.96/0.63  fof(f4,axiom,(
% 1.96/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.96/0.63  fof(f18,plain,(
% 1.96/0.63    r1_xboole_0(sK0,sK1)),
% 1.96/0.63    inference(cnf_transformation,[],[f14])).
% 1.96/0.63  fof(f14,plain,(
% 1.96/0.63    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1))),
% 1.96/0.63    inference(ennf_transformation,[],[f12])).
% 1.96/0.63  fof(f12,negated_conjecture,(
% 1.96/0.63    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.96/0.63    inference(negated_conjecture,[],[f11])).
% 1.96/0.63  fof(f11,conjecture,(
% 1.96/0.63    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.96/0.63  fof(f32,plain,(
% 1.96/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.96/0.63    inference(cnf_transformation,[],[f9])).
% 1.96/0.63  fof(f9,axiom,(
% 1.96/0.63    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.96/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.96/0.63  fof(f33,plain,(
% 1.96/0.63    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.96/0.63    inference(definition_unfolding,[],[f19,f25,f25])).
% 1.96/0.63  fof(f19,plain,(
% 1.96/0.63    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)),
% 1.96/0.63    inference(cnf_transformation,[],[f14])).
% 1.96/0.63  % SZS output end Proof for theBenchmark
% 1.96/0.63  % (16008)------------------------------
% 1.96/0.63  % (16008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.63  % (16008)Termination reason: Refutation
% 1.96/0.63  
% 1.96/0.63  % (16008)Memory used [KB]: 6908
% 1.96/0.63  % (16008)Time elapsed: 0.194 s
% 1.96/0.63  % (16008)------------------------------
% 1.96/0.63  % (16008)------------------------------
% 1.96/0.64  % (15983)Success in time 0.268 s
%------------------------------------------------------------------------------
