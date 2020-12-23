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
% DateTime   : Thu Dec  3 12:48:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f29])).

fof(f29,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f14,f27])).

fof(f27,plain,(
    ! [X2] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X2) ),
    inference(global_subsumption,[],[f15,f25])).

fof(f25,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f23,f21])).

fof(f21,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f17,f16])).

fof(f16,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0)
      | k1_xboole_0 = k7_relat_1(X0,X1) ) ),
    inference(resolution,[],[f19,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_relat_1)).

fof(f15,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f14,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).

fof(f12,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (3505)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (3505)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0),
% 0.21/0.42    inference(superposition,[],[f14,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X2] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)) )),
% 0.21/0.42    inference(global_subsumption,[],[f15,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X2] : (~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X2)) )),
% 0.21/0.42    inference(resolution,[],[f23,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    v1_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(superposition,[],[f17,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) )),
% 0.21/0.42    inference(resolution,[],[f19,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : ((v1_relat_1(X0) & v1_xboole_0(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc17_relat_1)).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (3505)------------------------------
% 0.21/0.43  % (3505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (3500)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  % (3505)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (3505)Memory used [KB]: 6012
% 0.21/0.43  % (3505)Time elapsed: 0.005 s
% 0.21/0.43  % (3505)------------------------------
% 0.21/0.43  % (3505)------------------------------
% 0.21/0.43  % (3494)Success in time 0.071 s
%------------------------------------------------------------------------------
