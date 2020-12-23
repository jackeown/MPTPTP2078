%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 270 expanded)
%              Number of leaves         :    9 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :   81 ( 497 expanded)
%              Number of equality atoms :   71 ( 468 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(global_subsumption,[],[f97,f99])).

fof(f99,plain,(
    sK1 = k1_enumset1(sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f96,f33])).

fof(f33,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f16,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f96,plain,(
    k1_enumset1(sK0,sK0,sK0) = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f29,f90])).

fof(f90,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f30,f31,f84,f89])).

fof(f89,plain,
    ( sK2 = k1_enumset1(sK0,sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f80,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
      | k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f22,f28,f28])).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f21])).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f80,plain,(
    r1_tarski(sK2,k1_enumset1(sK0,sK0,sK0)) ),
    inference(superposition,[],[f64,f29])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f46,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f19,f21,f21])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(unit_resulting_resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f18,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f84,plain,
    ( sK1 = k1_enumset1(sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,(
    r1_tarski(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f47,f26])).

fof(f47,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    inference(superposition,[],[f34,f29])).

fof(f31,plain,
    ( sK2 != k1_enumset1(sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f13,f28])).

fof(f13,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f30,plain,
    ( sK2 != k1_enumset1(sK0,sK0,sK0)
    | sK1 != k1_enumset1(sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f14,f28,f28])).

fof(f14,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    k1_enumset1(sK0,sK0,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f15,f28,f27])).

fof(f15,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f97,plain,(
    sK1 != k1_enumset1(sK0,sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 != k1_enumset1(sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f32,f90])).

fof(f32,plain,
    ( sK1 != k1_enumset1(sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f12,f28])).

fof(f12,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (31295)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (31279)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (31287)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (31282)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (31269)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (31269)Refutation not found, incomplete strategy% (31269)------------------------------
% 0.21/0.52  % (31269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31269)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31269)Memory used [KB]: 1663
% 0.21/0.52  % (31269)Time elapsed: 0.105 s
% 0.21/0.52  % (31269)------------------------------
% 0.21/0.52  % (31269)------------------------------
% 0.21/0.52  % (31271)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (31272)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (31286)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (31283)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (31279)Refutation not found, incomplete strategy% (31279)------------------------------
% 0.21/0.52  % (31279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31279)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31279)Memory used [KB]: 10618
% 0.21/0.52  % (31279)Time elapsed: 0.117 s
% 0.21/0.52  % (31279)------------------------------
% 0.21/0.52  % (31279)------------------------------
% 0.21/0.52  % (31288)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (31273)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (31273)Refutation not found, incomplete strategy% (31273)------------------------------
% 0.21/0.53  % (31273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31273)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31273)Memory used [KB]: 6268
% 0.21/0.53  % (31273)Time elapsed: 0.119 s
% 0.21/0.53  % (31273)------------------------------
% 0.21/0.53  % (31273)------------------------------
% 0.21/0.53  % (31275)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (31297)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (31293)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (31296)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (31274)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (31270)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (31293)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(global_subsumption,[],[f97,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    sK1 = k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f96,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f16,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f20,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK0,sK0) = k3_tarski(k1_enumset1(sK1,sK1,k1_xboole_0))),
% 0.21/0.53    inference(backward_demodulation,[],[f29,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    k1_xboole_0 = sK2),
% 0.21/0.53    inference(global_subsumption,[],[f30,f31,f84,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    sK2 = k1_enumset1(sK0,sK0,sK0) | k1_xboole_0 = sK2),
% 0.21/0.53    inference(resolution,[],[f80,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,k1_enumset1(X1,X1,X1)) | k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f28,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f17,f21])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    r1_tarski(sK2,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.53    inference(superposition,[],[f64,f29])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 0.21/0.53    inference(superposition,[],[f46,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f21,f21])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f34,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f18,f27])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    sK1 = k1_enumset1(sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 0.21/0.53    inference(resolution,[],[f38,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    r1_tarski(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f47,f26])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    k1_xboole_0 = k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.53    inference(superposition,[],[f34,f29])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    sK2 != k1_enumset1(sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.21/0.53    inference(definition_unfolding,[],[f13,f28])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    sK2 != k1_enumset1(sK0,sK0,sK0) | sK1 != k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.53    inference(definition_unfolding,[],[f14,f28,f28])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    k1_enumset1(sK0,sK0,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK2))),
% 0.21/0.53    inference(definition_unfolding,[],[f15,f28,f27])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    sK1 != k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    k1_xboole_0 != k1_xboole_0 | sK1 != k1_enumset1(sK0,sK0,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f32,f90])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    sK1 != k1_enumset1(sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 0.21/0.53    inference(definition_unfolding,[],[f12,f28])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (31293)------------------------------
% 0.21/0.53  % (31293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31293)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (31293)Memory used [KB]: 6268
% 0.21/0.53  % (31293)Time elapsed: 0.132 s
% 0.21/0.53  % (31293)------------------------------
% 0.21/0.53  % (31293)------------------------------
% 0.21/0.53  % (31271)Refutation not found, incomplete strategy% (31271)------------------------------
% 0.21/0.53  % (31271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31271)Memory used [KB]: 10618
% 0.21/0.53  % (31271)Time elapsed: 0.125 s
% 0.21/0.53  % (31271)------------------------------
% 0.21/0.53  % (31271)------------------------------
% 0.21/0.53  % (31274)Refutation not found, incomplete strategy% (31274)------------------------------
% 0.21/0.53  % (31274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31274)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31274)Memory used [KB]: 6268
% 0.21/0.53  % (31274)Time elapsed: 0.128 s
% 0.21/0.53  % (31274)------------------------------
% 0.21/0.53  % (31274)------------------------------
% 0.21/0.54  % (31268)Success in time 0.178 s
%------------------------------------------------------------------------------
