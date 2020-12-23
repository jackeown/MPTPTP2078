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
% DateTime   : Thu Dec  3 12:48:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   19 (  26 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  40 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(global_subsumption,[],[f11,f23])).

fof(f23,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f20,f16])).

fof(f16,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f12,f15])).

fof(f15,plain,(
    v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f9])).

fof(f9,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK0) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f20,plain,(
    k1_xboole_0 = k4_relat_1(sK0) ),
    inference(resolution,[],[f19,f15])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k4_relat_1(X0) ) ),
    inference(resolution,[],[f13,f12])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

fof(f11,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f5])).

fof(f5,negated_conjecture,(
    k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:50:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (31870)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (31871)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (31869)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (31868)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (31868)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(global_subsumption,[],[f11,f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(forward_demodulation,[],[f20,f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    k1_xboole_0 = sK0),
% 0.22/0.44    inference(resolution,[],[f12,f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    v1_xboole_0(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    v1_xboole_0(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f2,f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK0)),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    k1_xboole_0 = k4_relat_1(sK0)),
% 0.22/0.44    inference(resolution,[],[f19,f15])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k4_relat_1(X0)) )),
% 0.22/0.44    inference(resolution,[],[f13,f12])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(flattening,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (31868)------------------------------
% 0.22/0.44  % (31868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (31868)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (31868)Memory used [KB]: 6012
% 0.22/0.44  % (31868)Time elapsed: 0.004 s
% 0.22/0.44  % (31868)------------------------------
% 0.22/0.44  % (31868)------------------------------
% 0.22/0.44  % (31863)Success in time 0.075 s
%------------------------------------------------------------------------------
