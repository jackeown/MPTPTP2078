%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  30 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  46 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f15])).

fof(f15,plain,(
    o_0_0_xboole_0 != k4_relat_1(o_0_0_xboole_0) ),
    inference(superposition,[],[f10,f14])).

fof(f14,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f12,f11])).

fof(f11,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f10,plain,(
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

fof(f18,plain,(
    o_0_0_xboole_0 = k4_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[],[f17,f11])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = k4_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f16,f14])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k4_relat_1(X0) ) ),
    inference(resolution,[],[f13,f12])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k4_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (9985)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.41  % (9985)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(subsumption_resolution,[],[f18,f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    o_0_0_xboole_0 != k4_relat_1(o_0_0_xboole_0)),
% 0.20/0.41    inference(superposition,[],[f10,f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    o_0_0_xboole_0 = k1_xboole_0),
% 0.20/0.41    inference(resolution,[],[f12,f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    v1_xboole_0(o_0_0_xboole_0)),
% 0.20/0.41    inference(cnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    v1_xboole_0(o_0_0_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(cnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,plain,(
% 0.20/0.41    k1_xboole_0 != k4_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(flattening,[],[f5])).
% 0.20/0.41  fof(f5,negated_conjecture,(
% 0.20/0.41    ~k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.41    inference(negated_conjecture,[],[f4])).
% 0.20/0.41  fof(f4,conjecture,(
% 0.20/0.41    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    o_0_0_xboole_0 = k4_relat_1(o_0_0_xboole_0)),
% 0.20/0.41    inference(resolution,[],[f17,f11])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = k4_relat_1(X0)) )),
% 0.20/0.41    inference(forward_demodulation,[],[f16,f14])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k4_relat_1(X0)) )),
% 0.20/0.41    inference(resolution,[],[f13,f12])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k4_relat_1(X0)))),
% 0.20/0.41    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (9985)------------------------------
% 0.20/0.41  % (9985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (9985)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (9985)Memory used [KB]: 10490
% 0.20/0.41  % (9985)Time elapsed: 0.004 s
% 0.20/0.41  % (9985)------------------------------
% 0.20/0.41  % (9985)------------------------------
% 0.20/0.41  % (9980)Success in time 0.063 s
%------------------------------------------------------------------------------
