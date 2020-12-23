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
% DateTime   : Thu Dec  3 12:49:51 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   36 (  72 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :   72 ( 137 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f57,f63])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f61,f12])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

fof(f61,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(resolution,[],[f53,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f53,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_2
  <=> v1_relat_1(k7_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f55,f12])).

fof(f55,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f49,f15])).

fof(f49,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_1
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f44,f51,f47])).

% (24651)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f44,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f36,f13])).

fof(f13,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1)))
      | ~ v1_relat_1(k7_relat_1(sK2,X1))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(forward_demodulation,[],[f32,f18])).

fof(f18,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(resolution,[],[f16,f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k2_relat_1(k7_relat_1(sK2,k6_subset_1(X0,X1))))
      | ~ v1_relat_1(k7_relat_1(sK2,X1))
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] : k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) = k7_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(resolution,[],[f17,f12])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0)),k2_relat_1(k6_subset_1(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0))))
      | ~ v1_relat_1(k7_relat_1(sK2,X0))
      | ~ v1_relat_1(k7_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f20,f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(k7_relat_1(sK2,X0),X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(superposition,[],[f14,f18])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:20:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.43  % (24644)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.23/0.43  % (24644)Refutation found. Thanks to Tanya!
% 0.23/0.43  % SZS status Theorem for theBenchmark
% 0.23/0.43  % SZS output start Proof for theBenchmark
% 0.23/0.43  fof(f64,plain,(
% 0.23/0.43    $false),
% 0.23/0.43    inference(avatar_sat_refutation,[],[f54,f57,f63])).
% 0.23/0.43  fof(f63,plain,(
% 0.23/0.43    spl3_2),
% 0.23/0.43    inference(avatar_contradiction_clause,[],[f62])).
% 0.23/0.43  fof(f62,plain,(
% 0.23/0.43    $false | spl3_2),
% 0.23/0.43    inference(subsumption_resolution,[],[f61,f12])).
% 0.23/0.43  fof(f12,plain,(
% 0.23/0.43    v1_relat_1(sK2)),
% 0.23/0.43    inference(cnf_transformation,[],[f7])).
% 0.23/0.43  fof(f7,plain,(
% 0.23/0.43    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 0.23/0.43    inference(ennf_transformation,[],[f6])).
% 0.23/0.43  fof(f6,negated_conjecture,(
% 0.23/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.23/0.43    inference(negated_conjecture,[],[f5])).
% 0.23/0.43  fof(f5,conjecture,(
% 0.23/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).
% 0.23/0.43  fof(f61,plain,(
% 0.23/0.43    ~v1_relat_1(sK2) | spl3_2),
% 0.23/0.43    inference(resolution,[],[f53,f15])).
% 0.23/0.43  fof(f15,plain,(
% 0.23/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f9])).
% 0.23/0.43  fof(f9,plain,(
% 0.23/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.23/0.43    inference(ennf_transformation,[],[f1])).
% 0.23/0.43  fof(f1,axiom,(
% 0.23/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.23/0.43  fof(f53,plain,(
% 0.23/0.43    ~v1_relat_1(k7_relat_1(sK2,sK1)) | spl3_2),
% 0.23/0.43    inference(avatar_component_clause,[],[f51])).
% 0.23/0.43  fof(f51,plain,(
% 0.23/0.43    spl3_2 <=> v1_relat_1(k7_relat_1(sK2,sK1))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.43  fof(f57,plain,(
% 0.23/0.43    spl3_1),
% 0.23/0.43    inference(avatar_contradiction_clause,[],[f56])).
% 0.23/0.43  fof(f56,plain,(
% 0.23/0.43    $false | spl3_1),
% 0.23/0.43    inference(subsumption_resolution,[],[f55,f12])).
% 0.23/0.43  fof(f55,plain,(
% 0.23/0.43    ~v1_relat_1(sK2) | spl3_1),
% 0.23/0.43    inference(resolution,[],[f49,f15])).
% 0.23/0.43  fof(f49,plain,(
% 0.23/0.43    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_1),
% 0.23/0.43    inference(avatar_component_clause,[],[f47])).
% 0.23/0.43  fof(f47,plain,(
% 0.23/0.43    spl3_1 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.23/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.43  fof(f54,plain,(
% 0.23/0.43    ~spl3_1 | ~spl3_2),
% 0.23/0.43    inference(avatar_split_clause,[],[f44,f51,f47])).
% 0.23/0.43  % (24651)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.23/0.43  fof(f44,plain,(
% 0.23/0.43    ~v1_relat_1(k7_relat_1(sK2,sK1)) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.23/0.43    inference(resolution,[],[f36,f13])).
% 0.23/0.43  fof(f13,plain,(
% 0.23/0.43    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 0.23/0.43    inference(cnf_transformation,[],[f7])).
% 0.23/0.43  fof(f36,plain,(
% 0.23/0.43    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k9_relat_1(sK2,k6_subset_1(X0,X1))) | ~v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.23/0.43    inference(forward_demodulation,[],[f32,f18])).
% 0.23/0.43  fof(f18,plain,(
% 0.23/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.23/0.43    inference(resolution,[],[f16,f12])).
% 0.23/0.43  fof(f16,plain,(
% 0.23/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f10])).
% 0.23/0.43  fof(f10,plain,(
% 0.23/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.23/0.43    inference(ennf_transformation,[],[f3])).
% 0.23/0.43  fof(f3,axiom,(
% 0.23/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.23/0.43  fof(f32,plain,(
% 0.23/0.43    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)),k2_relat_1(k7_relat_1(sK2,k6_subset_1(X0,X1)))) | ~v1_relat_1(k7_relat_1(sK2,X1)) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.23/0.43    inference(superposition,[],[f22,f26])).
% 0.23/0.43  fof(f26,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k6_subset_1(k7_relat_1(sK2,X0),k7_relat_1(sK2,X1)) = k7_relat_1(sK2,k6_subset_1(X0,X1))) )),
% 0.23/0.43    inference(resolution,[],[f17,f12])).
% 0.23/0.43  fof(f17,plain,(
% 0.23/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f11])).
% 0.23/0.43  fof(f11,plain,(
% 0.23/0.43    ! [X0,X1,X2] : (k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.23/0.43    inference(ennf_transformation,[],[f2])).
% 0.23/0.43  fof(f2,axiom,(
% 0.23/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_relat_1)).
% 0.23/0.43  fof(f22,plain,(
% 0.23/0.43    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK2,X1),k9_relat_1(sK2,X0)),k2_relat_1(k6_subset_1(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0)))) | ~v1_relat_1(k7_relat_1(sK2,X0)) | ~v1_relat_1(k7_relat_1(sK2,X1))) )),
% 0.23/0.43    inference(superposition,[],[f20,f18])).
% 0.23/0.43  fof(f20,plain,(
% 0.23/0.43    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k9_relat_1(sK2,X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(k7_relat_1(sK2,X0),X1))) | ~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.23/0.43    inference(superposition,[],[f14,f18])).
% 0.23/0.43  fof(f14,plain,(
% 0.23/0.43    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f8])).
% 0.23/0.43  fof(f8,plain,(
% 0.23/0.43    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.23/0.43    inference(ennf_transformation,[],[f4])).
% 0.23/0.43  fof(f4,axiom,(
% 0.23/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relat_1)).
% 0.23/0.43  % SZS output end Proof for theBenchmark
% 0.23/0.43  % (24644)------------------------------
% 0.23/0.43  % (24644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.43  % (24644)Termination reason: Refutation
% 0.23/0.43  
% 0.23/0.43  % (24644)Memory used [KB]: 10618
% 0.23/0.43  % (24644)Time elapsed: 0.007 s
% 0.23/0.43  % (24644)------------------------------
% 0.23/0.43  % (24644)------------------------------
% 0.23/0.44  % (24642)Success in time 0.07 s
%------------------------------------------------------------------------------
