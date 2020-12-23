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
% DateTime   : Thu Dec  3 12:51:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 (  76 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :  108 ( 241 expanded)
%              Number of equality atoms :   37 ( 100 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f24,f29,f34,f38,f44,f48,f52])).

fof(f52,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f18,plain,
    ( k9_relat_1(sK1,sK0) != k9_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl3_1
  <=> k9_relat_1(sK1,sK0) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( k9_relat_1(sK1,sK0) = k9_relat_1(sK2,sK0)
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f49,f47])).

fof(f47,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_7
  <=> ! [X1] : k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f49,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(superposition,[],[f43,f23])).

fof(f23,plain,
    ( k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl3_2
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f43,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_6
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f48,plain,
    ( spl3_7
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f40,f36,f31,f46])).

fof(f31,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f36,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f40,plain,
    ( ! [X1] : k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f31])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f44,plain,
    ( spl3_6
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f39,f36,f26,f42])).

fof(f26,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f39,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f26])).

fof(f38,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f14,f36])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f34,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f10,f31])).

fof(f10,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k9_relat_1(sK1,sK0) != k9_relat_1(sK2,sK0)
    & k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
            & k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k9_relat_1(sK1,sK0) != k9_relat_1(X2,sK0)
          & k7_relat_1(sK1,sK0) = k7_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,
    ( ? [X2] :
        ( k9_relat_1(sK1,sK0) != k9_relat_1(X2,sK0)
        & k7_relat_1(sK1,sK0) = k7_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( k9_relat_1(sK1,sK0) != k9_relat_1(sK2,sK0)
      & k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
          & k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k9_relat_1(X1,X0) != k9_relat_1(X2,X0)
          & k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
             => k9_relat_1(X1,X0) = k9_relat_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
           => k9_relat_1(X1,X0) = k9_relat_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_relat_1)).

fof(f29,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f11,f26])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f21])).

fof(f12,plain,(
    k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f13,f16])).

fof(f13,plain,(
    k9_relat_1(sK1,sK0) != k9_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:19:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (11159)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (11160)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (11159)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f19,f24,f29,f34,f38,f44,f48,f52])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f51])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    $false | (spl3_1 | ~spl3_2 | ~spl3_6 | ~spl3_7)),
% 0.22/0.43    inference(subsumption_resolution,[],[f50,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    k9_relat_1(sK1,sK0) != k9_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    spl3_1 <=> k9_relat_1(sK1,sK0) = k9_relat_1(sK2,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    k9_relat_1(sK1,sK0) = k9_relat_1(sK2,sK0) | (~spl3_2 | ~spl3_6 | ~spl3_7)),
% 0.22/0.43    inference(forward_demodulation,[],[f49,f47])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X1] : (k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)) ) | ~spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f46])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl3_7 <=> ! [X1] : k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    k9_relat_1(sK2,sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) | (~spl3_2 | ~spl3_6)),
% 0.22/0.43    inference(superposition,[],[f43,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    spl3_2 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl3_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl3_6 <=> ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl3_7 | ~spl3_4 | ~spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f40,f36,f31,f46])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    spl3_4 <=> v1_relat_1(sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    spl3_5 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X1] : (k2_relat_1(k7_relat_1(sK1,X1)) = k9_relat_1(sK1,X1)) ) | (~spl3_4 | ~spl3_5)),
% 0.22/0.43    inference(resolution,[],[f37,f33])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    v1_relat_1(sK1) | ~spl3_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f31])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f36])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl3_6 | ~spl3_3 | ~spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f39,f36,f26,f42])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | (~spl3_3 | ~spl3_5)),
% 0.22/0.43    inference(resolution,[],[f37,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f26])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f36])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl3_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f10,f31])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    v1_relat_1(sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    (k9_relat_1(sK1,sK0) != k9_relat_1(sK2,sK0) & k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8,f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1] : (? [X2] : (k9_relat_1(X1,X0) != k9_relat_1(X2,X0) & k7_relat_1(X1,X0) = k7_relat_1(X2,X0) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (k9_relat_1(sK1,sK0) != k9_relat_1(X2,sK0) & k7_relat_1(sK1,sK0) = k7_relat_1(X2,sK0) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X2] : (k9_relat_1(sK1,sK0) != k9_relat_1(X2,sK0) & k7_relat_1(sK1,sK0) = k7_relat_1(X2,sK0) & v1_relat_1(X2)) => (k9_relat_1(sK1,sK0) != k9_relat_1(sK2,sK0) & k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f5,plain,(
% 0.22/0.43    ? [X0,X1] : (? [X2] : (k9_relat_1(X1,X0) != k9_relat_1(X2,X0) & k7_relat_1(X1,X0) = k7_relat_1(X2,X0) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f4])).
% 0.22/0.43  fof(f4,plain,(
% 0.22/0.43    ? [X0,X1] : (? [X2] : ((k9_relat_1(X1,X0) != k9_relat_1(X2,X0) & k7_relat_1(X1,X0) = k7_relat_1(X2,X0)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k7_relat_1(X1,X0) = k7_relat_1(X2,X0) => k9_relat_1(X1,X0) = k9_relat_1(X2,X0))))),
% 0.22/0.43    inference(negated_conjecture,[],[f2])).
% 0.22/0.43  fof(f2,conjecture,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k7_relat_1(X1,X0) = k7_relat_1(X2,X0) => k9_relat_1(X1,X0) = k9_relat_1(X2,X0))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_relat_1)).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl3_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f11,f26])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    v1_relat_1(sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    spl3_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f12,f21])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    k7_relat_1(sK1,sK0) = k7_relat_1(sK2,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ~spl3_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f13,f16])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    k9_relat_1(sK1,sK0) != k9_relat_1(sK2,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (11159)------------------------------
% 0.22/0.43  % (11159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (11159)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (11159)Memory used [KB]: 10490
% 0.22/0.43  % (11159)Time elapsed: 0.006 s
% 0.22/0.43  % (11159)------------------------------
% 0.22/0.43  % (11159)------------------------------
% 0.22/0.43  % (11152)Success in time 0.071 s
%------------------------------------------------------------------------------
