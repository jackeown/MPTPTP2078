%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  28 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  48 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f11])).

fof(f11,plain,(
    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k9_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f23,plain,(
    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f22,f13])).

fof(f13,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f22,plain,(
    k2_relat_1(k1_xboole_0) = k9_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[],[f18,f21])).

fof(f21,plain,(
    k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f19,f10])).

fof(f10,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f16,f14])).

fof(f14,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f18,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    inference(resolution,[],[f15,f10])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (29352)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (29352)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f23,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    k1_xboole_0 != k9_relat_1(sK0,k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0] : (k1_xboole_0 != k9_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,negated_conjecture,(
% 0.20/0.42    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.20/0.42    inference(negated_conjecture,[],[f5])).
% 0.20/0.42  fof(f5,conjecture,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    k1_xboole_0 = k9_relat_1(sK0,k1_xboole_0)),
% 0.20/0.42    inference(forward_demodulation,[],[f22,f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    k2_relat_1(k1_xboole_0) = k9_relat_1(sK0,k1_xboole_0)),
% 0.20/0.42    inference(superposition,[],[f18,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    k1_xboole_0 = k7_relat_1(sK0,k1_xboole_0)),
% 0.20/0.42    inference(resolution,[],[f19,f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    v1_relat_1(sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 0.20/0.42    inference(resolution,[],[f16,f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) )),
% 0.20/0.42    inference(resolution,[],[f15,f10])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (29352)------------------------------
% 0.20/0.42  % (29352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (29352)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (29352)Memory used [KB]: 10490
% 0.20/0.42  % (29352)Time elapsed: 0.005 s
% 0.20/0.42  % (29352)------------------------------
% 0.20/0.42  % (29352)------------------------------
% 0.20/0.42  % (29351)Success in time 0.067 s
%------------------------------------------------------------------------------
