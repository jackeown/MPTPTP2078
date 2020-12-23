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
% DateTime   : Thu Dec  3 12:38:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 705 expanded)
%              Number of leaves         :   11 ( 225 expanded)
%              Depth                    :   19
%              Number of atoms          :  101 ( 954 expanded)
%              Number of equality atoms :   62 ( 765 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f358,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f357,f21])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f357,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f354,f87])).

fof(f87,plain,(
    r1_tarski(sK1,sK1) ),
    inference(backward_demodulation,[],[f78,f85])).

fof(f85,plain,(
    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f29,f43,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f78,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f72,f45])).

fof(f45,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f72,plain,(
    ! [X0] : r1_tarski(sK1,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(sK0,sK0,sK0,sK0)))) ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f31,f43,f43])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X0)
      | r1_tarski(sK1,k3_tarski(k2_enumset1(X1,X1,X1,X0))) ) ),
    inference(resolution,[],[f64,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f64,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X0) ) ),
    inference(superposition,[],[f52,f44])).

fof(f44,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f42,f43])).

fof(f20,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f354,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f348,f94])).

fof(f94,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | sK1 = X2
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f49,f85])).

fof(f348,plain,(
    ! [X2] :
      ( r1_tarski(sK2,X2)
      | ~ r1_tarski(sK1,X2) ) ),
    inference(superposition,[],[f52,f340])).

fof(f340,plain,(
    sK1 = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK1)) ),
    inference(forward_demodulation,[],[f334,f45])).

fof(f334,plain,(
    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1)) = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK1)) ),
    inference(superposition,[],[f128,f111])).

fof(f111,plain,(
    ! [X1] : k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,X1)))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X1)) ),
    inference(superposition,[],[f50,f91])).

fof(f91,plain,(
    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(backward_demodulation,[],[f44,f85])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_tarski(k2_enumset1(k3_tarski(k2_enumset1(X0,X0,X0,X1)),k3_tarski(k2_enumset1(X0,X0,X0,X1)),k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2)) = k3_tarski(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) ),
    inference(definition_unfolding,[],[f33,f42,f42,f42,f42])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f128,plain,(
    ! [X2] : k3_tarski(k2_enumset1(X2,X2,X2,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_tarski(k2_enumset1(X2,X2,X2,sK1)))) ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f88,plain,(
    ! [X0] : r1_tarski(sK1,k3_tarski(k2_enumset1(X0,X0,X0,sK1))) ),
    inference(backward_demodulation,[],[f72,f85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:22:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (6354)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (6355)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (6374)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (6372)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (6362)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (6366)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (6352)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (6366)Refutation not found, incomplete strategy% (6366)------------------------------
% 0.22/0.53  % (6366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6366)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6366)Memory used [KB]: 6140
% 0.22/0.53  % (6366)Time elapsed: 0.003 s
% 0.22/0.53  % (6366)------------------------------
% 0.22/0.53  % (6366)------------------------------
% 0.22/0.53  % (6358)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (6371)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (6353)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (6379)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (6372)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f359,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f358,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    k1_xboole_0 != sK2),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.22/0.54    inference(negated_conjecture,[],[f12])).
% 0.22/0.54  fof(f12,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.22/0.54  fof(f358,plain,(
% 0.22/0.54    k1_xboole_0 = sK2),
% 0.22/0.54    inference(subsumption_resolution,[],[f357,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    sK1 != sK2),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f357,plain,(
% 0.22/0.54    sK1 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.54    inference(subsumption_resolution,[],[f354,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    r1_tarski(sK1,sK1)),
% 0.22/0.54    inference(backward_demodulation,[],[f78,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f80,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    k1_xboole_0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 0.22/0.54    inference(resolution,[],[f78,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f29,f43,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f24,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f27,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.54    inference(superposition,[],[f72,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.22/0.54    inference(definition_unfolding,[],[f25,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f26,f41])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.54    inference(rectify,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_enumset1(X0,X0,X0,k2_enumset1(sK0,sK0,sK0,sK0))))) )),
% 0.22/0.54    inference(resolution,[],[f66,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f31,f43,f43])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X0) | r1_tarski(sK1,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )),
% 0.22/0.54    inference(resolution,[],[f64,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f34,f42])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(sK1,X0) | ~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X0)) )),
% 0.22/0.54    inference(superposition,[],[f52,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.54    inference(definition_unfolding,[],[f20,f42,f43])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f35,f42])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK1) | sK1 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.54    inference(resolution,[],[f348,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X2] : (~r1_tarski(X2,sK1) | sK1 = X2 | k1_xboole_0 = X2) )),
% 0.22/0.54    inference(superposition,[],[f49,f85])).
% 0.22/0.54  fof(f348,plain,(
% 0.22/0.54    ( ! [X2] : (r1_tarski(sK2,X2) | ~r1_tarski(sK1,X2)) )),
% 0.22/0.54    inference(superposition,[],[f52,f340])).
% 0.22/0.54  fof(f340,plain,(
% 0.22/0.54    sK1 = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK1))),
% 0.22/0.54    inference(forward_demodulation,[],[f334,f45])).
% 0.22/0.54  fof(f334,plain,(
% 0.22/0.54    k3_tarski(k2_enumset1(sK1,sK1,sK1,sK1)) = k3_tarski(k2_enumset1(sK2,sK2,sK2,sK1))),
% 0.22/0.54    inference(superposition,[],[f128,f111])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ( ! [X1] : (k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_tarski(k2_enumset1(sK2,sK2,sK2,X1)))) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X1))) )),
% 0.22/0.54    inference(superposition,[],[f50,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 0.22/0.54    inference(backward_demodulation,[],[f44,f85])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k3_tarski(k2_enumset1(k3_tarski(k2_enumset1(X0,X0,X0,X1)),k3_tarski(k2_enumset1(X0,X0,X0,X1)),k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2)) = k3_tarski(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f33,f42,f42,f42,f42])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    ( ! [X2] : (k3_tarski(k2_enumset1(X2,X2,X2,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_tarski(k2_enumset1(X2,X2,X2,sK1))))) )),
% 0.22/0.54    inference(resolution,[],[f88,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f42])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(sK1,k3_tarski(k2_enumset1(X0,X0,X0,sK1)))) )),
% 0.22/0.54    inference(backward_demodulation,[],[f72,f85])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (6372)------------------------------
% 0.22/0.54  % (6372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6372)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (6372)Memory used [KB]: 1918
% 0.22/0.54  % (6372)Time elapsed: 0.125 s
% 0.22/0.54  % (6372)------------------------------
% 0.22/0.54  % (6372)------------------------------
% 0.22/0.54  % (6380)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (6350)Success in time 0.178 s
%------------------------------------------------------------------------------
