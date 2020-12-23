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
% DateTime   : Thu Dec  3 12:51:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  72 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 150 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f100,f254])).

fof(f254,plain,
    ( ~ spl2_2
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl2_2
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f99,f248])).

fof(f248,plain,
    ( ! [X7] : k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X7))) = k6_subset_1(k1_relat_1(sK1),X7)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f240,f70])).

fof(f70,plain,
    ( ! [X0] : k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f45,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(f45,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f240,plain,
    ( ! [X7] : k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X7))) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X7)))
    | ~ spl2_2 ),
    inference(superposition,[],[f70,f232])).

fof(f232,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f78,f50])).

fof(f50,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f47,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f47,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK1,X0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f45,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f78,plain,
    ( ! [X0] : k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f45,f62,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f62,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f45,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f99,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_5
  <=> k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f100,plain,
    ( ~ spl2_5
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f94,f43,f38,f97])).

fof(f38,plain,
    ( spl2_1
  <=> k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f94,plain,
    ( k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f40,f70])).

fof(f40,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

fof(f41,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f23,f38])).

fof(f23,plain,(
    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:14:37 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.46  % (10934)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (10943)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (10934)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f41,f46,f100,f254])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ~spl2_2 | spl2_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f250])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    $false | (~spl2_2 | spl2_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f99,f248])).
% 0.21/0.48  fof(f248,plain,(
% 0.21/0.48    ( ! [X7] : (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X7))) = k6_subset_1(k1_relat_1(sK1),X7)) ) | ~spl2_2),
% 0.21/0.48    inference(forward_demodulation,[],[f240,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0)) ) | ~spl2_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f45,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ( ! [X7] : (k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,X7))) = k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X7)))) ) | ~spl2_2),
% 0.21/0.48    inference(superposition,[],[f70,f232])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_2),
% 0.21/0.48    inference(forward_demodulation,[],[f78,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f47,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) ) | ~spl2_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f45,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X0] : (k7_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0)))) ) | ~spl2_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f45,f62,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),X0)) ) | ~spl2_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f45,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) | spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl2_5 <=> k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ~spl2_5 | spl2_1 | ~spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f94,f43,f38,f97])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl2_1 <=> k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) = k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),sK0) | (spl2_1 | ~spl2_2)),
% 0.21/0.48    inference(backward_demodulation,[],[f40,f70])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) | spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f43])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) != k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),k1_relat_1(k7_relat_1(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f38])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) != k6_subset_1(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (10934)------------------------------
% 0.21/0.48  % (10934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10934)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (10934)Memory used [KB]: 6268
% 0.21/0.48  % (10934)Time elapsed: 0.042 s
% 0.21/0.48  % (10934)------------------------------
% 0.21/0.48  % (10934)------------------------------
% 0.21/0.48  % (10921)Success in time 0.119 s
%------------------------------------------------------------------------------
