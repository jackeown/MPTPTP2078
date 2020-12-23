%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:50 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  39 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f36])).

fof(f36,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f12,f35])).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f34,f17])).

fof(f17,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f25,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f25,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f24,f21])).

fof(f21,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f16,f13])).

fof(f13,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f16,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f24,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f18,f14])).

fof(f14,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f12,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:07:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.40  % (17265)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.12/0.40  % (17266)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.12/0.40  % (17272)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.12/0.40  % (17265)Refutation found. Thanks to Tanya!
% 0.12/0.40  % SZS status Theorem for theBenchmark
% 0.12/0.40  % SZS output start Proof for theBenchmark
% 0.12/0.40  fof(f39,plain,(
% 0.12/0.40    $false),
% 0.12/0.40    inference(trivial_inequality_removal,[],[f36])).
% 0.12/0.40  fof(f36,plain,(
% 0.12/0.40    k1_xboole_0 != k1_xboole_0),
% 0.12/0.40    inference(superposition,[],[f12,f35])).
% 0.12/0.40  fof(f35,plain,(
% 0.12/0.40    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f34,f17])).
% 0.12/0.40  fof(f17,plain,(
% 0.12/0.40    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f2])).
% 0.12/0.40  fof(f2,axiom,(
% 0.12/0.40    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.12/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.12/0.40  fof(f34,plain,(
% 0.12/0.40    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.12/0.40    inference(resolution,[],[f25,f20])).
% 0.12/0.40  fof(f20,plain,(
% 0.12/0.40    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f11])).
% 0.12/0.40  fof(f11,plain,(
% 0.12/0.40    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.12/0.40    inference(ennf_transformation,[],[f1])).
% 0.12/0.40  fof(f1,axiom,(
% 0.12/0.40    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.12/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.12/0.40  fof(f25,plain,(
% 0.12/0.40    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.12/0.40    inference(subsumption_resolution,[],[f24,f21])).
% 0.12/0.40  fof(f21,plain,(
% 0.12/0.40    v1_relat_1(k1_xboole_0)),
% 0.12/0.40    inference(superposition,[],[f16,f13])).
% 0.12/0.40  fof(f13,plain,(
% 0.12/0.40    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.12/0.40    inference(cnf_transformation,[],[f5])).
% 0.12/0.40  fof(f5,axiom,(
% 0.12/0.40    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.12/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.12/0.40  fof(f16,plain,(
% 0.12/0.40    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.12/0.40    inference(cnf_transformation,[],[f3])).
% 0.12/0.40  fof(f3,axiom,(
% 0.12/0.40    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.12/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.12/0.40  fof(f24,plain,(
% 0.12/0.40    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.12/0.40    inference(superposition,[],[f18,f14])).
% 0.12/0.40  fof(f14,plain,(
% 0.12/0.40    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.12/0.40    inference(cnf_transformation,[],[f4])).
% 0.12/0.40  fof(f4,axiom,(
% 0.12/0.40    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.12/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.12/0.40  fof(f18,plain,(
% 0.12/0.40    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.12/0.40    inference(cnf_transformation,[],[f10])).
% 0.12/0.40  fof(f10,plain,(
% 0.12/0.40    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.12/0.40    inference(ennf_transformation,[],[f6])).
% 0.12/0.40  fof(f6,axiom,(
% 0.12/0.40    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.12/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.12/0.40  fof(f12,plain,(
% 0.12/0.40    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.12/0.40    inference(cnf_transformation,[],[f9])).
% 0.12/0.40  fof(f9,plain,(
% 0.12/0.40    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.12/0.40    inference(ennf_transformation,[],[f8])).
% 0.12/0.40  fof(f8,negated_conjecture,(
% 0.12/0.40    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.12/0.40    inference(negated_conjecture,[],[f7])).
% 0.12/0.40  fof(f7,conjecture,(
% 0.12/0.40    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.12/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.12/0.40  % SZS output end Proof for theBenchmark
% 0.12/0.40  % (17265)------------------------------
% 0.12/0.40  % (17265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.40  % (17265)Termination reason: Refutation
% 0.12/0.40  
% 0.12/0.40  % (17265)Memory used [KB]: 10490
% 0.12/0.40  % (17265)Time elapsed: 0.005 s
% 0.12/0.40  % (17265)------------------------------
% 0.12/0.40  % (17265)------------------------------
% 0.12/0.41  % (17264)Success in time 0.062 s
%------------------------------------------------------------------------------
