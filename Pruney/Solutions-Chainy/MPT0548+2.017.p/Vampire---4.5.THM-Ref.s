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
% DateTime   : Thu Dec  3 12:49:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  60 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f36,f39])).

fof(f39,plain,(
    ~ spl1_1 ),
    inference(avatar_contradiction_clause,[],[f38])).

fof(f38,plain,
    ( $false
    | ~ spl1_1 ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f29,plain,
    ( ! [X1] : ~ v1_relat_1(X1)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl1_1
  <=> ! [X1] : ~ v1_relat_1(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f36,plain,(
    ~ spl1_2 ),
    inference(avatar_contradiction_clause,[],[f35])).

fof(f35,plain,
    ( $false
    | ~ spl1_2 ),
    inference(trivial_inequality_removal,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl1_2 ),
    inference(superposition,[],[f14,f32])).

fof(f32,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl1_2
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f33,plain,
    ( spl1_1
    | spl1_2 ),
    inference(avatar_split_clause,[],[f26,f31,f28])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f25,f16])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f24,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:30:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (7045)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (7038)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  % (7038)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f33,f36,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ~spl1_1),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    $false | ~spl1_1),
% 0.21/0.43    inference(resolution,[],[f29,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X1] : (~v1_relat_1(X1)) ) | ~spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    spl1_1 <=> ! [X1] : ~v1_relat_1(X1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ~spl1_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f35])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    $false | ~spl1_2),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | ~spl1_2),
% 0.21/0.43    inference(superposition,[],[f14,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl1_2 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl1_1 | spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f31,f28])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f25,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f24,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k7_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(resolution,[],[f22,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X2)) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(resolution,[],[f20,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (7038)------------------------------
% 0.21/0.43  % (7038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (7038)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (7038)Memory used [KB]: 10618
% 0.21/0.43  % (7038)Time elapsed: 0.005 s
% 0.21/0.43  % (7038)------------------------------
% 0.21/0.43  % (7038)------------------------------
% 0.21/0.43  % (7037)Success in time 0.072 s
%------------------------------------------------------------------------------
