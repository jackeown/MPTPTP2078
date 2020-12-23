%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,plain,(
    $false ),
    inference(global_subsumption,[],[f9,f16])).

fof(f16,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f15,f10])).

fof(f10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k4_relat_1(X0) ) ),
    inference(resolution,[],[f12,f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f12,plain,(
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

fof(f9,plain,(
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (28583)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (28578)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % (28583)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(global_subsumption,[],[f9,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(resolution,[],[f15,f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k4_relat_1(X0)) )),
% 0.21/0.42    inference(resolution,[],[f12,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(flattening,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (28583)------------------------------
% 0.21/0.42  % (28583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (28583)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (28583)Memory used [KB]: 6012
% 0.21/0.42  % (28583)Time elapsed: 0.003 s
% 0.21/0.42  % (28583)------------------------------
% 0.21/0.42  % (28583)------------------------------
% 0.21/0.42  % (28574)Success in time 0.063 s
%------------------------------------------------------------------------------
