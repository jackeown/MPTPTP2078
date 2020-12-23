%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  69 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   14
%              Number of atoms          :   97 ( 173 expanded)
%              Number of equality atoms :   62 ( 109 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(subsumption_resolution,[],[f228,f25])).

fof(f25,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f228,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f220,f26])).

fof(f26,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f220,plain,
    ( sK0 = sK3
    | sK0 = sK2 ),
    inference(resolution,[],[f219,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f219,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f160,f91])).

fof(f91,plain,(
    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f64,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f64,plain,(
    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f62,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f62,plain,(
    k2_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK0,sK1)) = k2_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0) ),
    inference(superposition,[],[f32,f50])).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f24,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f24,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f160,plain,(
    ! [X5] : r1_tarski(k1_tarski(sK0),k2_xboole_0(X5,k2_tarski(sK2,sK3))) ),
    inference(resolution,[],[f99,f46])).

fof(f46,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f99,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_tarski(sK0,sK1))
      | r1_tarski(X1,k2_xboole_0(X2,k2_tarski(sK2,sK3))) ) ),
    inference(resolution,[],[f94,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f94,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_tarski(sK2,sK3))
      | ~ r1_tarski(X0,k2_tarski(sK0,sK1)) ) ),
    inference(superposition,[],[f36,f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:29:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (5092)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (5086)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (5082)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (5098)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (5092)Refutation not found, incomplete strategy% (5092)------------------------------
% 0.22/0.53  % (5092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5092)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5092)Memory used [KB]: 10618
% 0.22/0.53  % (5092)Time elapsed: 0.122 s
% 0.22/0.53  % (5092)------------------------------
% 0.22/0.53  % (5092)------------------------------
% 0.22/0.54  % (5081)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (5083)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (5085)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (5095)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (5080)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (5080)Refutation not found, incomplete strategy% (5080)------------------------------
% 0.22/0.54  % (5080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (5080)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (5080)Memory used [KB]: 1663
% 0.22/0.54  % (5080)Time elapsed: 0.123 s
% 0.22/0.54  % (5080)------------------------------
% 0.22/0.54  % (5080)------------------------------
% 0.22/0.54  % (5090)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (5099)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (5104)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (5107)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (5098)Refutation not found, incomplete strategy% (5098)------------------------------
% 0.22/0.55  % (5098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5098)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5098)Memory used [KB]: 10618
% 0.22/0.55  % (5098)Time elapsed: 0.135 s
% 0.22/0.55  % (5098)------------------------------
% 0.22/0.55  % (5098)------------------------------
% 0.22/0.55  % (5082)Refutation not found, incomplete strategy% (5082)------------------------------
% 0.22/0.55  % (5082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5082)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5082)Memory used [KB]: 10746
% 0.22/0.55  % (5082)Time elapsed: 0.134 s
% 0.22/0.55  % (5082)------------------------------
% 0.22/0.55  % (5082)------------------------------
% 0.22/0.55  % (5090)Refutation not found, incomplete strategy% (5090)------------------------------
% 0.22/0.55  % (5090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5089)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (5087)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (5096)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (5091)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (5089)Refutation not found, incomplete strategy% (5089)------------------------------
% 0.22/0.55  % (5089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5089)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5089)Memory used [KB]: 10746
% 0.22/0.55  % (5089)Time elapsed: 0.134 s
% 0.22/0.55  % (5089)------------------------------
% 0.22/0.55  % (5089)------------------------------
% 0.22/0.55  % (5108)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (5088)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (5102)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (5090)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5090)Memory used [KB]: 10618
% 0.22/0.55  % (5090)Time elapsed: 0.137 s
% 0.22/0.55  % (5090)------------------------------
% 0.22/0.55  % (5090)------------------------------
% 0.22/0.55  % (5097)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (5105)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (5100)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (5094)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (5104)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f229,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f228,f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    sK0 != sK2),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.56    inference(negated_conjecture,[],[f13])).
% 0.22/0.56  fof(f13,conjecture,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    sK0 = sK2),
% 0.22/0.56    inference(subsumption_resolution,[],[f220,f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    sK0 != sK3),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f220,plain,(
% 0.22/0.56    sK0 = sK3 | sK0 = sK2),
% 0.22/0.56    inference(resolution,[],[f219,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.22/0.56  fof(f219,plain,(
% 0.22/0.56    r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3))),
% 0.22/0.56    inference(superposition,[],[f160,f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.56    inference(superposition,[],[f64,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK0,sK1))),
% 0.22/0.56    inference(forward_demodulation,[],[f62,f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    k2_xboole_0(k2_tarski(sK2,sK3),k2_tarski(sK0,sK1)) = k2_xboole_0(k2_tarski(sK2,sK3),k1_xboole_0)),
% 0.22/0.56    inference(superposition,[],[f32,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.56    inference(resolution,[],[f24,f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.56  fof(f160,plain,(
% 0.22/0.56    ( ! [X5] : (r1_tarski(k1_tarski(sK0),k2_xboole_0(X5,k2_tarski(sK2,sK3)))) )),
% 0.22/0.56    inference(resolution,[],[f99,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 0.22/0.56    inference(equality_resolution,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.56    inference(flattening,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.22/0.56    inference(nnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ( ! [X2,X1] : (~r1_tarski(X1,k2_tarski(sK0,sK1)) | r1_tarski(X1,k2_xboole_0(X2,k2_tarski(sK2,sK3)))) )),
% 0.22/0.56    inference(resolution,[],[f94,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(X0,k2_tarski(sK2,sK3)) | ~r1_tarski(X0,k2_tarski(sK0,sK1))) )),
% 0.22/0.56    inference(superposition,[],[f36,f64])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (5104)------------------------------
% 0.22/0.56  % (5104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (5104)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (5104)Memory used [KB]: 1918
% 0.22/0.56  % (5104)Time elapsed: 0.111 s
% 0.22/0.56  % (5104)------------------------------
% 0.22/0.56  % (5104)------------------------------
% 0.22/0.56  % (5077)Success in time 0.193 s
%------------------------------------------------------------------------------
