%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:09 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :   11
%              Number of atoms          :   48 (  50 expanded)
%              Number of equality atoms :   41 (  43 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36,f14])).

fof(f14,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f9])).

fof(f9,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f36,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f34,f17])).

fof(f17,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f34,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f33,f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f21,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f33,plain,(
    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f32,f15])).

fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f32,plain,(
    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f31,f16])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f19,f27])).

fof(f27,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f20,f25])).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f20,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (10821)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.50  % (10813)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (10830)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.51  % (10808)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (10811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (10811)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(subsumption_resolution,[],[f36,f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,plain,(
% 0.19/0.51    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(flattening,[],[f9])).
% 0.19/0.51  fof(f9,negated_conjecture,(
% 0.19/0.51    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(negated_conjecture,[],[f8])).
% 0.19/0.51  fof(f8,conjecture,(
% 0.19/0.51    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(forward_demodulation,[],[f34,f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.51    inference(superposition,[],[f33,f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.51    inference(superposition,[],[f21,f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.51    inference(forward_demodulation,[],[f32,f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 0.19/0.51    inference(forward_demodulation,[],[f31,f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 0.19/0.51    inference(resolution,[],[f19,f27])).
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    v1_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(superposition,[],[f20,f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.51    inference(equality_resolution,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f13])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.19/0.51    inference(flattening,[],[f12])).
% 1.19/0.51  fof(f12,plain,(
% 1.19/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.19/0.51    inference(nnf_transformation,[],[f4])).
% 1.19/0.51  fof(f4,axiom,(
% 1.19/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.19/0.51  fof(f20,plain,(
% 1.19/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f6])).
% 1.19/0.51  fof(f6,axiom,(
% 1.19/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.19/0.51  fof(f19,plain,(
% 1.19/0.51    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.19/0.51    inference(cnf_transformation,[],[f11])).
% 1.19/0.51  fof(f11,plain,(
% 1.19/0.51    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.19/0.51    inference(ennf_transformation,[],[f5])).
% 1.19/0.51  fof(f5,axiom,(
% 1.19/0.51    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.19/0.51  % SZS output end Proof for theBenchmark
% 1.19/0.51  % (10811)------------------------------
% 1.19/0.51  % (10811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (10811)Termination reason: Refutation
% 1.19/0.51  
% 1.19/0.51  % (10811)Memory used [KB]: 6140
% 1.19/0.51  % (10811)Time elapsed: 0.107 s
% 1.19/0.51  % (10811)------------------------------
% 1.19/0.51  % (10811)------------------------------
% 1.19/0.51  % (10816)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.19/0.51  % (10809)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.51  % (10812)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.19/0.51  % (10806)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.19/0.51  % (10807)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.19/0.51  % (10821)Refutation not found, incomplete strategy% (10821)------------------------------
% 1.19/0.51  % (10821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (10821)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (10821)Memory used [KB]: 10618
% 1.19/0.51  % (10821)Time elapsed: 0.107 s
% 1.19/0.51  % (10821)------------------------------
% 1.19/0.51  % (10821)------------------------------
% 1.19/0.51  % (10812)Refutation not found, incomplete strategy% (10812)------------------------------
% 1.19/0.51  % (10812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (10812)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (10812)Memory used [KB]: 10618
% 1.19/0.51  % (10812)Time elapsed: 0.107 s
% 1.19/0.51  % (10812)------------------------------
% 1.19/0.51  % (10812)------------------------------
% 1.19/0.51  % (10806)Refutation not found, incomplete strategy% (10806)------------------------------
% 1.19/0.51  % (10806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.51  % (10806)Termination reason: Refutation not found, incomplete strategy
% 1.19/0.51  
% 1.19/0.51  % (10806)Memory used [KB]: 10618
% 1.19/0.51  % (10806)Time elapsed: 0.110 s
% 1.19/0.51  % (10806)------------------------------
% 1.19/0.51  % (10806)------------------------------
% 1.19/0.51  % (10825)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.19/0.51  % (10827)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.19/0.51  % (10803)Success in time 0.16 s
%------------------------------------------------------------------------------
