%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:53 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 256 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :   89 ( 448 expanded)
%              Number of equality atoms :   53 ( 261 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f933,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f932])).

fof(f932,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f930,f862])).

fof(f862,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f233,f852])).

fof(f852,plain,(
    sK0 = sK3 ),
    inference(backward_demodulation,[],[f432,f850])).

fof(f850,plain,(
    sK0 = k2_xboole_0(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f836,f30])).

% (9412)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f836,plain,(
    r1_tarski(sK3,sK0) ),
    inference(forward_demodulation,[],[f808,f251])).

fof(f251,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f210,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f210,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f36,f103])).

fof(f103,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f20,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f808,plain,(
    r1_tarski(k4_xboole_0(sK3,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f302,f85])).

fof(f85,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X7,k2_xboole_0(X6,X5))
      | r1_tarski(k4_xboole_0(X7,X5),X6) ) ),
    inference(superposition,[],[f33,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f302,plain,(
    r1_tarski(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f41,f18])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f26])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f432,plain,(
    sK3 = k2_xboole_0(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f268,f46])).

fof(f46,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f30,f26])).

fof(f268,plain,(
    r1_tarski(sK0,sK3) ),
    inference(forward_demodulation,[],[f259,f229])).

% (9403)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f229,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f207,f23])).

fof(f207,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f36,f152])).

fof(f152,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f35,f102])).

fof(f102,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f19,f37])).

fof(f19,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f27,f27])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f259,plain,(
    r1_tarski(k4_xboole_0(sK0,sK2),sK3) ),
    inference(unit_resulting_resolution,[],[f24,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK0,sK1))
      | r1_tarski(k4_xboole_0(X0,sK2),sK3) ) ),
    inference(superposition,[],[f33,f18])).

fof(f233,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f208,f23])).

fof(f208,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f36,f153])).

fof(f153,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f35,f103])).

fof(f930,plain,(
    sK2 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f929,f238])).

fof(f238,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f209,f23])).

fof(f209,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f36,f102])).

fof(f929,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f858,f59])).

fof(f59,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3) ),
    inference(superposition,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f858,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) ),
    inference(backward_demodulation,[],[f57,f852])).

fof(f57,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f29,f18])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (9407)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (9418)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (9423)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (9408)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (9400)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (9415)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (9405)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (9405)Refutation not found, incomplete strategy% (9405)------------------------------
% 0.21/0.52  % (9405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9405)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9405)Memory used [KB]: 10618
% 0.21/0.52  % (9405)Time elapsed: 0.119 s
% 0.21/0.52  % (9405)------------------------------
% 0.21/0.52  % (9405)------------------------------
% 0.21/0.53  % (9395)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (9413)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.53  % (9420)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.53  % (9398)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.53  % (9396)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  % (9397)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.54  % (9399)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.54  % (9394)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.54  % (9410)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (9394)Refutation not found, incomplete strategy% (9394)------------------------------
% 1.36/0.54  % (9394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (9394)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (9394)Memory used [KB]: 1791
% 1.36/0.54  % (9394)Time elapsed: 0.135 s
% 1.36/0.54  % (9394)------------------------------
% 1.36/0.54  % (9394)------------------------------
% 1.36/0.54  % (9421)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (9406)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.54  % (9411)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (9417)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.54  % (9411)Refutation not found, incomplete strategy% (9411)------------------------------
% 1.36/0.54  % (9411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (9411)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (9411)Memory used [KB]: 10618
% 1.36/0.54  % (9411)Time elapsed: 0.137 s
% 1.36/0.54  % (9411)------------------------------
% 1.36/0.54  % (9411)------------------------------
% 1.36/0.55  % (9418)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f933,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(global_subsumption,[],[f21,f932])).
% 1.36/0.55  fof(f932,plain,(
% 1.36/0.55    sK1 = sK2),
% 1.36/0.55    inference(backward_demodulation,[],[f930,f862])).
% 1.36/0.55  fof(f862,plain,(
% 1.36/0.55    sK1 = k4_xboole_0(sK1,sK0)),
% 1.36/0.55    inference(backward_demodulation,[],[f233,f852])).
% 1.36/0.55  fof(f852,plain,(
% 1.36/0.55    sK0 = sK3),
% 1.36/0.55    inference(backward_demodulation,[],[f432,f850])).
% 1.36/0.55  fof(f850,plain,(
% 1.36/0.55    sK0 = k2_xboole_0(sK3,sK0)),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f836,f30])).
% 1.36/0.55  % (9412)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.36/0.55  fof(f30,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,plain,(
% 1.36/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.36/0.55    inference(ennf_transformation,[],[f4])).
% 1.36/0.55  fof(f4,axiom,(
% 1.36/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.36/0.55  fof(f836,plain,(
% 1.36/0.55    r1_tarski(sK3,sK0)),
% 1.36/0.55    inference(forward_demodulation,[],[f808,f251])).
% 1.36/0.55  fof(f251,plain,(
% 1.36/0.55    sK3 = k4_xboole_0(sK3,sK1)),
% 1.36/0.55    inference(forward_demodulation,[],[f210,f23])).
% 1.36/0.55  fof(f23,plain,(
% 1.36/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f6])).
% 1.36/0.55  fof(f6,axiom,(
% 1.36/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.36/0.55  fof(f210,plain,(
% 1.36/0.55    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 1.36/0.55    inference(superposition,[],[f36,f103])).
% 1.36/0.55  fof(f103,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f20,f37])).
% 1.36/0.55  fof(f37,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.55    inference(definition_unfolding,[],[f32,f27])).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f10])).
% 1.36/0.55  fof(f10,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f3])).
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.36/0.55  fof(f20,plain,(
% 1.36/0.55    r1_xboole_0(sK3,sK1)),
% 1.36/0.55    inference(cnf_transformation,[],[f15])).
% 1.36/0.55  fof(f15,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.36/0.55    inference(flattening,[],[f14])).
% 1.36/0.55  fof(f14,plain,(
% 1.36/0.55    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.36/0.55    inference(ennf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,negated_conjecture,(
% 1.36/0.55    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.36/0.55    inference(negated_conjecture,[],[f12])).
% 1.36/0.55  fof(f12,conjecture,(
% 1.36/0.55    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.36/0.55  fof(f36,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f28,f27])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.36/0.55  fof(f808,plain,(
% 1.36/0.55    r1_tarski(k4_xboole_0(sK3,sK1),sK0)),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f302,f85])).
% 1.36/0.55  fof(f85,plain,(
% 1.36/0.55    ( ! [X6,X7,X5] : (~r1_tarski(X7,k2_xboole_0(X6,X5)) | r1_tarski(k4_xboole_0(X7,X5),X6)) )),
% 1.36/0.55    inference(superposition,[],[f33,f26])).
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f1])).
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f17])).
% 1.36/0.55  fof(f17,plain,(
% 1.36/0.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.36/0.55    inference(ennf_transformation,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.36/0.55  fof(f302,plain,(
% 1.36/0.55    r1_tarski(sK3,k2_xboole_0(sK0,sK1))),
% 1.36/0.55    inference(superposition,[],[f41,f18])).
% 1.36/0.55  fof(f18,plain,(
% 1.36/0.55    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.36/0.55    inference(cnf_transformation,[],[f15])).
% 1.36/0.55  fof(f41,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.36/0.55    inference(superposition,[],[f24,f26])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.36/0.55  fof(f432,plain,(
% 1.36/0.55    sK3 = k2_xboole_0(sK3,sK0)),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f268,f46])).
% 1.36/0.55  fof(f46,plain,(
% 1.36/0.55    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 1.36/0.55    inference(superposition,[],[f30,f26])).
% 1.36/0.55  fof(f268,plain,(
% 1.36/0.55    r1_tarski(sK0,sK3)),
% 1.36/0.55    inference(forward_demodulation,[],[f259,f229])).
% 1.36/0.55  % (9403)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.55  fof(f229,plain,(
% 1.36/0.55    sK0 = k4_xboole_0(sK0,sK2)),
% 1.36/0.55    inference(forward_demodulation,[],[f207,f23])).
% 1.36/0.55  fof(f207,plain,(
% 1.36/0.55    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.36/0.55    inference(superposition,[],[f36,f152])).
% 1.36/0.55  fof(f152,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.36/0.55    inference(superposition,[],[f35,f102])).
% 1.36/0.55  fof(f102,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f19,f37])).
% 1.36/0.55  fof(f19,plain,(
% 1.36/0.55    r1_xboole_0(sK2,sK0)),
% 1.36/0.55    inference(cnf_transformation,[],[f15])).
% 1.36/0.55  fof(f35,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.36/0.55    inference(definition_unfolding,[],[f25,f27,f27])).
% 1.36/0.55  fof(f25,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.36/0.55  fof(f259,plain,(
% 1.36/0.55    r1_tarski(k4_xboole_0(sK0,sK2),sK3)),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f24,f82])).
% 1.36/0.55  fof(f82,plain,(
% 1.36/0.55    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(X0,sK2),sK3)) )),
% 1.36/0.55    inference(superposition,[],[f33,f18])).
% 1.36/0.55  fof(f233,plain,(
% 1.36/0.55    sK1 = k4_xboole_0(sK1,sK3)),
% 1.36/0.55    inference(forward_demodulation,[],[f208,f23])).
% 1.36/0.55  fof(f208,plain,(
% 1.36/0.55    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.36/0.55    inference(superposition,[],[f36,f153])).
% 1.36/0.55  fof(f153,plain,(
% 1.36/0.55    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.36/0.55    inference(superposition,[],[f35,f103])).
% 1.36/0.55  fof(f930,plain,(
% 1.36/0.55    sK2 = k4_xboole_0(sK1,sK0)),
% 1.36/0.55    inference(forward_demodulation,[],[f929,f238])).
% 1.36/0.55  fof(f238,plain,(
% 1.36/0.55    sK2 = k4_xboole_0(sK2,sK0)),
% 1.36/0.55    inference(forward_demodulation,[],[f209,f23])).
% 1.36/0.55  fof(f209,plain,(
% 1.36/0.55    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.36/0.55    inference(superposition,[],[f36,f102])).
% 1.36/0.55  fof(f929,plain,(
% 1.36/0.55    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0)),
% 1.36/0.55    inference(forward_demodulation,[],[f858,f59])).
% 1.36/0.55  fof(f59,plain,(
% 1.36/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3)) )),
% 1.36/0.55    inference(superposition,[],[f29,f26])).
% 1.36/0.55  fof(f29,plain,(
% 1.36/0.55    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f7])).
% 1.36/0.55  fof(f7,axiom,(
% 1.36/0.55    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.36/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.36/0.55  fof(f858,plain,(
% 1.36/0.55    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)),
% 1.36/0.55    inference(backward_demodulation,[],[f57,f852])).
% 1.36/0.55  fof(f57,plain,(
% 1.36/0.55    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.36/0.55    inference(superposition,[],[f29,f18])).
% 1.36/0.55  fof(f21,plain,(
% 1.36/0.55    sK1 != sK2),
% 1.36/0.55    inference(cnf_transformation,[],[f15])).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (9418)------------------------------
% 1.36/0.55  % (9418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (9418)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (9418)Memory used [KB]: 6780
% 1.36/0.55  % (9418)Time elapsed: 0.080 s
% 1.36/0.55  % (9418)------------------------------
% 1.36/0.55  % (9418)------------------------------
% 1.36/0.55  % (9393)Success in time 0.19 s
%------------------------------------------------------------------------------
