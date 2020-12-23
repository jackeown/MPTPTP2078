%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:35 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 284 expanded)
%              Number of leaves         :    8 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 523 expanded)
%              Number of equality atoms :   32 ( 114 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(global_subsumption,[],[f203,f288])).

fof(f288,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f284,f187])).

fof(f187,plain,(
    k1_xboole_0 = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f98,f180])).

fof(f180,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f167,f166])).

fof(f166,plain,(
    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f53,f116,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sP3(sK2(X0,X1),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f116,plain,(
    ! [X0] : ~ sP3(X0,k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f113,f32])).

fof(f32,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0)
      | ~ sP3(X2,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f113,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f107,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP3(X2,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f107,plain,(
    ! [X0] : ~ sP3(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f21,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f167,plain,(
    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f113,f116,f36])).

fof(f98,plain,(
    k1_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f64,f73])).

fof(f73,plain,(
    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f48,f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f21,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f64,plain,(
    k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f50,f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f48,f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f284,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f204,f278,f36])).

fof(f278,plain,(
    ! [X2] : ~ r2_hidden(X2,k2_relat_1(k1_xboole_0)) ),
    inference(global_subsumption,[],[f21,f50,f277])).

fof(f277,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(X2,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f273,f182])).

fof(f182,plain,(
    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f73,f180])).

fof(f273,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
      | ~ v1_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[],[f124,f63])).

fof(f63,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f48,f26])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(k2_relat_1(X1)) ) ),
    inference(resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(f204,plain,(
    ! [X0] : ~ sP3(X0,k4_relat_1(k4_relat_1(k1_xboole_0))) ),
    inference(global_subsumption,[],[f104,f113])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ sP3(X0,k4_relat_1(k4_relat_1(k1_xboole_0))) ) ),
    inference(superposition,[],[f46,f98])).

fof(f46,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ sP3(X2,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f203,plain,(
    k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f181])).

fof(f181,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f20,f180])).

fof(f20,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:32:47 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.55  % (8378)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (8370)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (8378)Refutation not found, incomplete strategy% (8378)------------------------------
% 0.22/0.55  % (8378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8378)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8378)Memory used [KB]: 1663
% 0.22/0.55  % (8378)Time elapsed: 0.070 s
% 0.22/0.55  % (8378)------------------------------
% 0.22/0.55  % (8378)------------------------------
% 0.22/0.56  % (8362)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.56/0.57  % (8379)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.57  % (8361)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.56/0.57  % (8357)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.56/0.58  % (8360)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.56/0.58  % (8367)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.58  % (8371)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.80/0.59  % (8355)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.80/0.59  % (8355)Refutation not found, incomplete strategy% (8355)------------------------------
% 1.80/0.59  % (8355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.59  % (8355)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.59  
% 1.80/0.59  % (8355)Memory used [KB]: 1663
% 1.80/0.59  % (8355)Time elapsed: 0.161 s
% 1.80/0.59  % (8355)------------------------------
% 1.80/0.59  % (8355)------------------------------
% 1.80/0.59  % (8356)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.80/0.59  % (8363)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.80/0.60  % (8358)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.80/0.60  % (8359)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.80/0.60  % (8363)Refutation not found, incomplete strategy% (8363)------------------------------
% 1.80/0.60  % (8363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.60  % (8363)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.60  % (8384)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.80/0.60  
% 1.80/0.60  % (8363)Memory used [KB]: 10618
% 1.80/0.60  % (8363)Time elapsed: 0.169 s
% 1.80/0.60  % (8363)------------------------------
% 1.80/0.60  % (8363)------------------------------
% 1.80/0.60  % (8357)Refutation not found, incomplete strategy% (8357)------------------------------
% 1.80/0.60  % (8357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.60  % (8357)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.60  
% 1.80/0.60  % (8357)Memory used [KB]: 10618
% 1.80/0.60  % (8357)Time elapsed: 0.144 s
% 1.80/0.60  % (8357)------------------------------
% 1.80/0.60  % (8357)------------------------------
% 1.80/0.60  % (8379)Refutation found. Thanks to Tanya!
% 1.80/0.60  % SZS status Theorem for theBenchmark
% 1.80/0.60  % SZS output start Proof for theBenchmark
% 1.80/0.60  fof(f289,plain,(
% 1.80/0.60    $false),
% 1.80/0.60    inference(global_subsumption,[],[f203,f288])).
% 1.80/0.60  fof(f288,plain,(
% 1.80/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.80/0.60    inference(forward_demodulation,[],[f284,f187])).
% 1.80/0.60  fof(f187,plain,(
% 1.80/0.60    k1_xboole_0 = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))),
% 1.80/0.60    inference(backward_demodulation,[],[f98,f180])).
% 1.80/0.60  fof(f180,plain,(
% 1.80/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.80/0.60    inference(backward_demodulation,[],[f167,f166])).
% 1.80/0.60  fof(f166,plain,(
% 1.80/0.60    k1_xboole_0 = k1_relat_1(k1_relat_1(k1_xboole_0))),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f53,f116,f36])).
% 1.80/0.60  fof(f36,plain,(
% 1.80/0.60    ( ! [X0,X1] : (sP3(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.80/0.60    inference(cnf_transformation,[],[f8])).
% 1.80/0.60  fof(f8,axiom,(
% 1.80/0.60    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.80/0.60  fof(f116,plain,(
% 1.80/0.60    ( ! [X0] : (~sP3(X0,k1_relat_1(k1_xboole_0))) )),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f113,f32])).
% 1.80/0.60  fof(f32,plain,(
% 1.80/0.60    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK4(X0,X2)),X0) | ~sP3(X2,X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f8])).
% 1.80/0.60  fof(f113,plain,(
% 1.80/0.60    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f107,f45])).
% 1.80/0.60  fof(f45,plain,(
% 1.80/0.60    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | sP3(X2,X0)) )),
% 1.80/0.60    inference(equality_resolution,[],[f35])).
% 1.80/0.60  fof(f35,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (sP3(X2,X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.80/0.60    inference(cnf_transformation,[],[f8])).
% 1.80/0.60  fof(f107,plain,(
% 1.80/0.60    ( ! [X0] : (~sP3(X0,k1_xboole_0)) )),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f53,f32])).
% 1.80/0.60  fof(f53,plain,(
% 1.80/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f21,f29])).
% 1.80/0.60  fof(f29,plain,(
% 1.80/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f1])).
% 1.80/0.60  fof(f1,axiom,(
% 1.80/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.80/0.60  fof(f21,plain,(
% 1.80/0.60    v1_xboole_0(k1_xboole_0)),
% 1.80/0.60    inference(cnf_transformation,[],[f2])).
% 1.80/0.60  fof(f2,axiom,(
% 1.80/0.60    v1_xboole_0(k1_xboole_0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.80/0.60  fof(f167,plain,(
% 1.80/0.60    k1_relat_1(k1_xboole_0) = k1_relat_1(k1_relat_1(k1_xboole_0))),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f113,f116,f36])).
% 1.80/0.60  fof(f98,plain,(
% 1.80/0.60    k1_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))),
% 1.80/0.60    inference(backward_demodulation,[],[f64,f73])).
% 1.80/0.60  fof(f73,plain,(
% 1.80/0.60    k1_relat_1(k1_xboole_0) = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f48,f27])).
% 1.80/0.60  fof(f27,plain,(
% 1.80/0.60    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f17])).
% 1.80/0.60  fof(f17,plain,(
% 1.80/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.80/0.60    inference(ennf_transformation,[],[f11])).
% 1.80/0.60  fof(f11,axiom,(
% 1.80/0.60    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 1.80/0.60  fof(f48,plain,(
% 1.80/0.60    v1_relat_1(k1_xboole_0)),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f21,f24])).
% 1.80/0.60  fof(f24,plain,(
% 1.80/0.60    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f15])).
% 1.80/0.60  fof(f15,plain,(
% 1.80/0.60    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.80/0.60    inference(ennf_transformation,[],[f7])).
% 1.80/0.60  fof(f7,axiom,(
% 1.80/0.60    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.80/0.60  fof(f64,plain,(
% 1.80/0.60    k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f50,f26])).
% 1.80/0.60  fof(f26,plain,(
% 1.80/0.60    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f17])).
% 1.80/0.60  fof(f50,plain,(
% 1.80/0.60    v1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f48,f25])).
% 1.80/0.60  fof(f25,plain,(
% 1.80/0.60    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f16])).
% 1.80/0.60  fof(f16,plain,(
% 1.80/0.60    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.80/0.60    inference(ennf_transformation,[],[f9])).
% 1.80/0.60  fof(f9,axiom,(
% 1.80/0.60    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.80/0.60  fof(f284,plain,(
% 1.80/0.60    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f204,f278,f36])).
% 1.80/0.60  fof(f278,plain,(
% 1.80/0.60    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(k1_xboole_0))) )),
% 1.80/0.60    inference(global_subsumption,[],[f21,f50,f277])).
% 1.80/0.60  fof(f277,plain,(
% 1.80/0.60    ( ! [X2] : (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(X2,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k1_xboole_0))) )),
% 1.80/0.60    inference(forward_demodulation,[],[f273,f182])).
% 1.80/0.60  fof(f182,plain,(
% 1.80/0.60    k1_xboole_0 = k2_relat_1(k4_relat_1(k1_xboole_0))),
% 1.80/0.60    inference(backward_demodulation,[],[f73,f180])).
% 1.80/0.60  fof(f273,plain,(
% 1.80/0.60    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_xboole_0(k2_relat_1(k4_relat_1(k1_xboole_0)))) )),
% 1.80/0.60    inference(superposition,[],[f124,f63])).
% 1.80/0.60  fof(f63,plain,(
% 1.80/0.60    k2_relat_1(k1_xboole_0) = k1_relat_1(k4_relat_1(k1_xboole_0))),
% 1.80/0.60    inference(unit_resulting_resolution,[],[f48,f26])).
% 1.80/0.60  fof(f124,plain,(
% 1.80/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_xboole_0(k2_relat_1(X1))) )),
% 1.80/0.60    inference(resolution,[],[f31,f29])).
% 1.80/0.60  fof(f31,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r2_hidden(sK1(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f19])).
% 1.80/0.60  fof(f19,plain,(
% 1.80/0.60    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.80/0.60    inference(flattening,[],[f18])).
% 1.80/0.60  fof(f18,plain,(
% 1.80/0.60    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.80/0.60    inference(ennf_transformation,[],[f10])).
% 1.80/0.60  fof(f10,axiom,(
% 1.80/0.60    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).
% 1.80/0.60  fof(f204,plain,(
% 1.80/0.60    ( ! [X0] : (~sP3(X0,k4_relat_1(k4_relat_1(k1_xboole_0)))) )),
% 1.80/0.60    inference(global_subsumption,[],[f104,f113])).
% 1.80/0.60  fof(f104,plain,(
% 1.80/0.60    ( ! [X0] : (r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~sP3(X0,k4_relat_1(k4_relat_1(k1_xboole_0)))) )),
% 1.80/0.60    inference(superposition,[],[f46,f98])).
% 1.80/0.60  fof(f46,plain,(
% 1.80/0.60    ( ! [X2,X0] : (r2_hidden(X2,k1_relat_1(X0)) | ~sP3(X2,X0)) )),
% 1.80/0.60    inference(equality_resolution,[],[f34])).
% 1.80/0.60  fof(f34,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (~sP3(X2,X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.80/0.60    inference(cnf_transformation,[],[f8])).
% 1.80/0.60  fof(f203,plain,(
% 1.80/0.60    k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 1.80/0.60    inference(trivial_inequality_removal,[],[f181])).
% 1.80/0.60  fof(f181,plain,(
% 1.80/0.60    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 1.80/0.60    inference(backward_demodulation,[],[f20,f180])).
% 1.80/0.60  fof(f20,plain,(
% 1.80/0.60    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.80/0.60    inference(cnf_transformation,[],[f14])).
% 1.80/0.60  fof(f14,plain,(
% 1.80/0.60    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.80/0.60    inference(ennf_transformation,[],[f13])).
% 1.80/0.60  fof(f13,negated_conjecture,(
% 1.80/0.60    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.80/0.60    inference(negated_conjecture,[],[f12])).
% 1.80/0.60  fof(f12,conjecture,(
% 1.80/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.80/0.60  % SZS output end Proof for theBenchmark
% 1.80/0.60  % (8379)------------------------------
% 1.80/0.60  % (8379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.60  % (8379)Termination reason: Refutation
% 1.80/0.60  
% 1.80/0.60  % (8379)Memory used [KB]: 6396
% 1.80/0.60  % (8379)Time elapsed: 0.157 s
% 1.80/0.60  % (8379)------------------------------
% 1.80/0.60  % (8379)------------------------------
% 1.80/0.60  % (8354)Success in time 0.238 s
%------------------------------------------------------------------------------
