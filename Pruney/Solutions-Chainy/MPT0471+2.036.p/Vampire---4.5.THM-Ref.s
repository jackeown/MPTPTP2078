%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:09 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 (  39 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (3195)Refutation not found, incomplete strategy% (3195)------------------------------
% (3195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f36,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35,f12])).

% (3195)Termination reason: Refutation not found, incomplete strategy

% (3195)Memory used [KB]: 10618
% (3195)Time elapsed: 0.105 s
% (3195)------------------------------
% (3195)------------------------------
fof(f12,plain,(
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

fof(f35,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f34,f16])).

fof(f16,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f34,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f33,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f33,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f32,f14])).

fof(f14,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f32,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f31,f13])).

fof(f13,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f23,f26])).

fof(f26,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f18,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f18,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f17,plain,(
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
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.22/0.52  % (3187)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.52  % (3193)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.52  % (3195)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.22/0.52  % (3193)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  % (3195)Refutation not found, incomplete strategy% (3195)------------------------------
% 1.22/0.52  % (3195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  fof(f36,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(subsumption_resolution,[],[f35,f12])).
% 1.22/0.52  % (3195)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (3195)Memory used [KB]: 10618
% 1.22/0.52  % (3195)Time elapsed: 0.105 s
% 1.22/0.52  % (3195)------------------------------
% 1.22/0.52  % (3195)------------------------------
% 1.22/0.52  fof(f12,plain,(
% 1.22/0.52    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(cnf_transformation,[],[f10])).
% 1.22/0.52  fof(f10,plain,(
% 1.22/0.52    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(flattening,[],[f9])).
% 1.22/0.52  fof(f9,negated_conjecture,(
% 1.22/0.52    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(negated_conjecture,[],[f8])).
% 1.22/0.52  fof(f8,conjecture,(
% 1.22/0.52    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 1.22/0.52  fof(f35,plain,(
% 1.22/0.52    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(forward_demodulation,[],[f34,f16])).
% 1.22/0.52  fof(f16,plain,(
% 1.22/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.22/0.52    inference(cnf_transformation,[],[f2])).
% 1.22/0.52  fof(f2,axiom,(
% 1.22/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.22/0.52  fof(f34,plain,(
% 1.22/0.52    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.22/0.52    inference(forward_demodulation,[],[f33,f15])).
% 1.22/0.52  fof(f15,plain,(
% 1.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f1])).
% 1.22/0.52  fof(f1,axiom,(
% 1.22/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.22/0.52  fof(f33,plain,(
% 1.22/0.52    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.22/0.52    inference(forward_demodulation,[],[f32,f14])).
% 1.22/0.52  fof(f14,plain,(
% 1.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(cnf_transformation,[],[f7])).
% 1.22/0.52  fof(f7,axiom,(
% 1.22/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.22/0.52  fof(f32,plain,(
% 1.22/0.52    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0))),
% 1.22/0.52    inference(forward_demodulation,[],[f31,f13])).
% 1.22/0.52  fof(f13,plain,(
% 1.22/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(cnf_transformation,[],[f7])).
% 1.22/0.52  fof(f31,plain,(
% 1.22/0.52    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))),
% 1.22/0.52    inference(resolution,[],[f23,f26])).
% 1.22/0.52  fof(f26,plain,(
% 1.22/0.52    v1_relat_1(k1_xboole_0)),
% 1.22/0.52    inference(superposition,[],[f18,f24])).
% 1.22/0.52  fof(f24,plain,(
% 1.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.22/0.52    inference(equality_resolution,[],[f22])).
% 1.22/0.52  fof(f22,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.22/0.52    inference(cnf_transformation,[],[f4])).
% 1.22/0.52  fof(f4,axiom,(
% 1.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.22/0.52  fof(f18,plain,(
% 1.22/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f6])).
% 1.22/0.52  fof(f6,axiom,(
% 1.22/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.22/0.52  fof(f23,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 1.22/0.52    inference(definition_unfolding,[],[f17,f19])).
% 1.22/0.52  fof(f19,plain,(
% 1.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f3])).
% 1.22/0.52  fof(f3,axiom,(
% 1.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.22/0.52  fof(f17,plain,(
% 1.22/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.22/0.52    inference(cnf_transformation,[],[f11])).
% 1.22/0.52  fof(f11,plain,(
% 1.22/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.22/0.52    inference(ennf_transformation,[],[f5])).
% 1.22/0.52  fof(f5,axiom,(
% 1.22/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.22/0.52  % SZS output end Proof for theBenchmark
% 1.22/0.52  % (3193)------------------------------
% 1.22/0.52  % (3193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (3193)Termination reason: Refutation
% 1.22/0.52  
% 1.22/0.52  % (3193)Memory used [KB]: 6140
% 1.22/0.52  % (3193)Time elapsed: 0.109 s
% 1.22/0.52  % (3193)------------------------------
% 1.22/0.52  % (3193)------------------------------
% 1.22/0.52  % (3186)Success in time 0.168 s
%------------------------------------------------------------------------------
