%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:17 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :   43 (  47 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f20,f29])).

fof(f29,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f28])).

fof(f28,plain,
    ( $false
    | spl1_1 ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1 ),
    inference(superposition,[],[f19,f26])).

fof(f26,plain,(
    ! [X2] : k1_xboole_0 = k8_relat_1(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f23,f14])).

fof(f14,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)
      | ~ v1_relat_1(k2_zfmisc_1(X0,X1)) ) ),
    inference(superposition,[],[f22,f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k8_relat_1(k1_xboole_0,k2_zfmisc_1(X0,X1)) = k8_relat_1(X2,k8_relat_1(k1_xboole_0,k2_zfmisc_1(X0,X1))) ),
    inference(resolution,[],[f21,f12])).

fof(f12,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,k2_zfmisc_1(X2,X3)) = k8_relat_1(X1,k8_relat_1(X0,k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f15,f14])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f19,plain,
    ( k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl1_1
  <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f20,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f11,f17])).

fof(f11,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.08  % Command    : run_vampire %s %d
% 0.07/0.28  % Computer   : n009.cluster.edu
% 0.07/0.28  % Model      : x86_64 x86_64
% 0.07/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.28  % Memory     : 8042.1875MB
% 0.07/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.28  % CPULimit   : 60
% 0.07/0.28  % WCLimit    : 600
% 0.07/0.28  % DateTime   : Tue Dec  1 12:52:41 EST 2020
% 0.07/0.28  % CPUTime    : 
% 0.13/0.35  % (18308)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.13/0.35  % (18316)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.13/0.35  % (18308)Refutation found. Thanks to Tanya!
% 0.13/0.35  % SZS status Theorem for theBenchmark
% 0.13/0.35  % SZS output start Proof for theBenchmark
% 0.13/0.35  fof(f30,plain,(
% 0.13/0.35    $false),
% 0.13/0.35    inference(avatar_sat_refutation,[],[f20,f29])).
% 0.13/0.35  fof(f29,plain,(
% 0.13/0.35    spl1_1),
% 0.13/0.35    inference(avatar_contradiction_clause,[],[f28])).
% 0.13/0.35  fof(f28,plain,(
% 0.13/0.35    $false | spl1_1),
% 0.13/0.35    inference(trivial_inequality_removal,[],[f27])).
% 0.13/0.35  fof(f27,plain,(
% 0.13/0.35    k1_xboole_0 != k1_xboole_0 | spl1_1),
% 0.13/0.35    inference(superposition,[],[f19,f26])).
% 0.13/0.35  fof(f26,plain,(
% 0.13/0.35    ( ! [X2] : (k1_xboole_0 = k8_relat_1(X2,k1_xboole_0)) )),
% 0.13/0.35    inference(subsumption_resolution,[],[f23,f14])).
% 0.13/0.35  fof(f14,plain,(
% 0.13/0.35    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.13/0.35    inference(cnf_transformation,[],[f2])).
% 0.13/0.35  fof(f2,axiom,(
% 0.13/0.35    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.13/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.13/0.35  fof(f23,plain,(
% 0.13/0.35    ( ! [X2,X0,X1] : (k1_xboole_0 = k8_relat_1(X2,k1_xboole_0) | ~v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.13/0.35    inference(superposition,[],[f22,f13])).
% 0.13/0.35  fof(f13,plain,(
% 0.13/0.35    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 0.13/0.35    inference(cnf_transformation,[],[f8])).
% 0.13/0.35  fof(f8,plain,(
% 0.13/0.35    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.13/0.35    inference(ennf_transformation,[],[f4])).
% 0.13/0.35  fof(f4,axiom,(
% 0.13/0.35    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.13/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).
% 0.13/0.35  fof(f22,plain,(
% 0.13/0.35    ( ! [X2,X0,X1] : (k8_relat_1(k1_xboole_0,k2_zfmisc_1(X0,X1)) = k8_relat_1(X2,k8_relat_1(k1_xboole_0,k2_zfmisc_1(X0,X1)))) )),
% 0.13/0.35    inference(resolution,[],[f21,f12])).
% 0.13/0.35  fof(f12,plain,(
% 0.13/0.35    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.13/0.35    inference(cnf_transformation,[],[f1])).
% 0.13/0.35  fof(f1,axiom,(
% 0.13/0.35    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.13/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.13/0.35  fof(f21,plain,(
% 0.13/0.35    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | k8_relat_1(X0,k2_zfmisc_1(X2,X3)) = k8_relat_1(X1,k8_relat_1(X0,k2_zfmisc_1(X2,X3)))) )),
% 0.13/0.35    inference(resolution,[],[f15,f14])).
% 0.13/0.35  fof(f15,plain,(
% 0.13/0.35    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.13/0.35    inference(cnf_transformation,[],[f10])).
% 0.13/0.35  fof(f10,plain,(
% 0.13/0.35    ! [X0,X1,X2] : (k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.13/0.35    inference(flattening,[],[f9])).
% 0.13/0.35  fof(f9,plain,(
% 0.13/0.35    ! [X0,X1,X2] : ((k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.13/0.35    inference(ennf_transformation,[],[f3])).
% 0.13/0.35  fof(f3,axiom,(
% 0.13/0.35    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.13/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).
% 0.13/0.35  fof(f19,plain,(
% 0.13/0.35    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) | spl1_1),
% 0.13/0.35    inference(avatar_component_clause,[],[f17])).
% 0.13/0.35  fof(f17,plain,(
% 0.13/0.35    spl1_1 <=> k1_xboole_0 = k8_relat_1(sK0,k1_xboole_0)),
% 0.13/0.35    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.13/0.35  fof(f20,plain,(
% 0.13/0.35    ~spl1_1),
% 0.13/0.35    inference(avatar_split_clause,[],[f11,f17])).
% 0.13/0.35  fof(f11,plain,(
% 0.13/0.35    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.13/0.35    inference(cnf_transformation,[],[f7])).
% 0.13/0.35  fof(f7,plain,(
% 0.13/0.35    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.13/0.35    inference(ennf_transformation,[],[f6])).
% 0.13/0.35  fof(f6,negated_conjecture,(
% 0.13/0.35    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.13/0.35    inference(negated_conjecture,[],[f5])).
% 0.13/0.35  fof(f5,conjecture,(
% 0.13/0.35    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.13/0.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).
% 0.13/0.35  % SZS output end Proof for theBenchmark
% 0.13/0.35  % (18308)------------------------------
% 0.13/0.35  % (18308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.35  % (18308)Termination reason: Refutation
% 0.13/0.35  
% 0.13/0.35  % (18308)Memory used [KB]: 10490
% 0.13/0.35  % (18308)Time elapsed: 0.025 s
% 0.13/0.35  % (18308)------------------------------
% 0.13/0.35  % (18308)------------------------------
% 0.13/0.35  % (18305)Success in time 0.06 s
%------------------------------------------------------------------------------
