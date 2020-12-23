%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 128 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   94 ( 281 expanded)
%              Number of equality atoms :   37 ( 121 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(resolution,[],[f110,f35])).

fof(f35,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

% (5532)Refutation not found, incomplete strategy% (5532)------------------------------
% (5532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5532)Termination reason: Refutation not found, incomplete strategy

% (5532)Memory used [KB]: 1663
% (5532)Time elapsed: 0.122 s
% (5532)------------------------------
% (5532)------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f110,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f37,f107])).

fof(f107,plain,(
    k1_tarski(sK0) = k1_tarski(sK1) ),
    inference(backward_demodulation,[],[f79,f78])).

fof(f78,plain,(
    k1_tarski(sK0) = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f52,f75,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f75,plain,(
    k1_xboole_0 != sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f57,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f57,plain,(
    k1_xboole_0 != k4_xboole_0(sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f54,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f54,plain,(
    ~ r1_tarski(sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f36,f36,f39,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0 ) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(sK2(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f39,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(unit_resulting_resolution,[],[f16,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f29])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f16,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

% (5508)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f36,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    r1_tarski(sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f36,f36,f39,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(sK2(X0,X1,X2),X1)
      | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0 ) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(sK2(X0,X1,X2),X1)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,(
    k1_tarski(sK1) = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f53,f75,f19])).

fof(f53,plain,(
    r1_tarski(sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f36,f36,f39,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0 ) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f15,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (5512)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.50  % (5504)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (5504)Refutation not found, incomplete strategy% (5504)------------------------------
% 0.20/0.50  % (5504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5504)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (5504)Memory used [KB]: 1663
% 0.20/0.50  % (5504)Time elapsed: 0.096 s
% 0.20/0.50  % (5504)------------------------------
% 0.20/0.50  % (5504)------------------------------
% 0.20/0.50  % (5528)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (5503)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (5517)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (5517)Refutation not found, incomplete strategy% (5517)------------------------------
% 0.20/0.51  % (5517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5517)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5517)Memory used [KB]: 1663
% 0.20/0.51  % (5517)Time elapsed: 0.069 s
% 0.20/0.51  % (5517)------------------------------
% 0.20/0.51  % (5517)------------------------------
% 0.20/0.51  % (5513)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (5521)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (5521)Refutation not found, incomplete strategy% (5521)------------------------------
% 0.20/0.51  % (5521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5521)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5521)Memory used [KB]: 1663
% 0.20/0.51  % (5521)Time elapsed: 0.109 s
% 0.20/0.51  % (5521)------------------------------
% 0.20/0.51  % (5521)------------------------------
% 0.20/0.51  % (5513)Refutation not found, incomplete strategy% (5513)------------------------------
% 0.20/0.51  % (5513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5513)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5513)Memory used [KB]: 10618
% 0.20/0.51  % (5513)Time elapsed: 0.109 s
% 0.20/0.51  % (5513)------------------------------
% 0.20/0.51  % (5513)------------------------------
% 0.20/0.51  % (5516)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (5526)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (5511)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (5506)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (5520)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (5509)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (5529)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (5529)Refutation not found, incomplete strategy% (5529)------------------------------
% 0.20/0.52  % (5529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5529)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5529)Memory used [KB]: 6140
% 0.20/0.52  % (5529)Time elapsed: 0.107 s
% 0.20/0.52  % (5529)------------------------------
% 0.20/0.52  % (5529)------------------------------
% 0.20/0.52  % (5505)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (5520)Refutation not found, incomplete strategy% (5520)------------------------------
% 0.20/0.52  % (5520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5520)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (5520)Memory used [KB]: 1663
% 0.20/0.52  % (5520)Time elapsed: 0.113 s
% 0.20/0.52  % (5520)------------------------------
% 0.20/0.52  % (5520)------------------------------
% 0.20/0.52  % (5525)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (5532)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (5510)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (5528)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(resolution,[],[f110,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  % (5532)Refutation not found, incomplete strategy% (5532)------------------------------
% 0.20/0.53  % (5532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5532)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (5532)Memory used [KB]: 1663
% 0.20/0.53  % (5532)Time elapsed: 0.122 s
% 0.20/0.53  % (5532)------------------------------
% 0.20/0.53  % (5532)------------------------------
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0))),
% 0.20/0.53    inference(backward_demodulation,[],[f37,f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    k1_tarski(sK0) = k1_tarski(sK1)),
% 0.20/0.53    inference(backward_demodulation,[],[f79,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    k1_tarski(sK0) = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f52,f75,f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    k1_xboole_0 != sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.53    inference(superposition,[],[f57,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    k1_xboole_0 != k4_xboole_0(sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f54,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ~r1_tarski(sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f36,f36,f39,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(sK2(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f28,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_tarski(sK2(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f16,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f17,f29])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  % (5508)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  fof(f10,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.53    inference(negated_conjecture,[],[f9])).
% 0.20/0.53  fof(f9,conjecture,(
% 0.20/0.53    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.20/0.53    inference(equality_resolution,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f7])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    r1_tarski(sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f36,f36,f39,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(sK2(X0,X1,X2),X1) | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f26,f29])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(sK2(X0,X1,X2),X1) | k3_xboole_0(X1,X2) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    k1_tarski(sK1) = sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f53,f75,f19])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    r1_tarski(sK2(k1_xboole_0,k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f36,f36,f39,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(sK2(X0,X1,X2),X2) | k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f27,f29])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(sK2(X0,X1,X2),X2) | k3_xboole_0(X1,X2) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f15,f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    sK0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (5528)------------------------------
% 0.20/0.53  % (5528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (5528)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (5528)Memory used [KB]: 6268
% 0.20/0.53  % (5528)Time elapsed: 0.120 s
% 0.20/0.53  % (5528)------------------------------
% 0.20/0.53  % (5528)------------------------------
% 0.20/0.53  % (5502)Success in time 0.171 s
%------------------------------------------------------------------------------
