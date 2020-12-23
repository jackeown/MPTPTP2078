%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  41 expanded)
%              Number of equality atoms :   22 (  24 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(subsumption_resolution,[],[f29,f14])).

fof(f14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f29,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f28,f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f28,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f27,f13])).

fof(f13,plain,(
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

fof(f27,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f26,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f22,f18])).

fof(f18,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f21,f17])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f26,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f24,f16])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f24,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f20,f15])).

fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:43:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (4342)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (4344)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (4337)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (4339)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (4338)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (4338)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f29,f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(resolution,[],[f28,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ~v1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f27,f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(flattening,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    k1_xboole_0 = k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(forward_demodulation,[],[f26,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(forward_demodulation,[],[f22,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(superposition,[],[f21,f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(forward_demodulation,[],[f24,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(superposition,[],[f20,f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (4338)------------------------------
% 0.20/0.48  % (4338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (4338)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (4338)Memory used [KB]: 1535
% 0.20/0.48  % (4338)Time elapsed: 0.064 s
% 0.20/0.48  % (4338)------------------------------
% 0.20/0.48  % (4338)------------------------------
% 0.20/0.48  % (4334)Success in time 0.121 s
%------------------------------------------------------------------------------
