%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 101 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :  163 ( 269 expanded)
%              Number of equality atoms :   36 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f42,f46,f52,f61,f68,f85,f97,f113])).

fof(f113,plain,
    ( spl3_1
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_1
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f111,f23])).

fof(f23,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl3_1
  <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f111,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f110,f51])).

fof(f51,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_7
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f110,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k2_relat_1(k7_relat_1(sK0,sK1))
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(superposition,[],[f96,f67])).

fof(f67,plain,
    ( k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_10
  <=> k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f96,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,sK2),X0)) = k9_relat_1(k7_relat_1(sK0,sK2),X0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_15
  <=> ! [X0] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,sK2),X0)) = k9_relat_1(k7_relat_1(sK0,sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f97,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f87,f75,f40,f95])).

fof(f40,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f75,plain,
    ( spl3_12
  <=> v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f87,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,sK2),X0)) = k9_relat_1(k7_relat_1(sK0,sK2),X0)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(resolution,[],[f76,f41])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f76,plain,
    ( v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f85,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_12 ),
    inference(subsumption_resolution,[],[f83,f33])).

fof(f33,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f83,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl3_4
    | spl3_12 ),
    inference(resolution,[],[f77,f37])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f77,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f75])).

fof(f68,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f62,f59,f31,f65])).

fof(f59,plain,
    ( spl3_9
  <=> ! [X0] :
        ( k7_relat_1(k7_relat_1(X0,sK2),sK1) = k7_relat_1(X0,sK1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f62,plain,
    ( k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f60,f33])).

fof(f60,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(k7_relat_1(X0,sK2),sK1) = k7_relat_1(X0,sK1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f59])).

fof(f61,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f57,f44,f26,f59])).

fof(f26,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f44,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f57,plain,
    ( ! [X0] :
        ( k7_relat_1(k7_relat_1(X0,sK2),sK1) = k7_relat_1(X0,sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f45,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
        | ~ v1_relat_1(X2) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f44])).

fof(f52,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f47,f40,f31,f50])).

fof(f47,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f41,f33])).

fof(f46,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f42,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f38,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f34,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f14,f31])).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(f29,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f21])).

fof(f16,plain,(
    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:27:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (7439)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (7440)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  % (7438)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (7438)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f114,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f24,f29,f34,f38,f42,f46,f52,f61,f68,f85,f97,f113])).
% 0.22/0.43  fof(f113,plain,(
% 0.22/0.43    spl3_1 | ~spl3_7 | ~spl3_10 | ~spl3_15),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f112])).
% 0.22/0.43  fof(f112,plain,(
% 0.22/0.43    $false | (spl3_1 | ~spl3_7 | ~spl3_10 | ~spl3_15)),
% 0.22/0.43    inference(subsumption_resolution,[],[f111,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) | spl3_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    spl3_1 <=> k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.43  fof(f111,plain,(
% 0.22/0.43    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) | (~spl3_7 | ~spl3_10 | ~spl3_15)),
% 0.22/0.43    inference(forward_demodulation,[],[f110,f51])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f50])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl3_7 <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f110,plain,(
% 0.22/0.43    k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k2_relat_1(k7_relat_1(sK0,sK1)) | (~spl3_10 | ~spl3_15)),
% 0.22/0.43    inference(superposition,[],[f96,f67])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1) | ~spl3_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f65])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    spl3_10 <=> k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.43  fof(f96,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(k7_relat_1(sK0,sK2),X0)) = k9_relat_1(k7_relat_1(sK0,sK2),X0)) ) | ~spl3_15),
% 0.22/0.43    inference(avatar_component_clause,[],[f95])).
% 0.22/0.43  fof(f95,plain,(
% 0.22/0.43    spl3_15 <=> ! [X0] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,sK2),X0)) = k9_relat_1(k7_relat_1(sK0,sK2),X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    spl3_15 | ~spl3_5 | ~spl3_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f87,f75,f40,f95])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl3_5 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    spl3_12 <=> v1_relat_1(k7_relat_1(sK0,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(k7_relat_1(sK0,sK2),X0)) = k9_relat_1(k7_relat_1(sK0,sK2),X0)) ) | (~spl3_5 | ~spl3_12)),
% 0.22/0.43    inference(resolution,[],[f76,f41])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f40])).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    v1_relat_1(k7_relat_1(sK0,sK2)) | ~spl3_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f75])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    ~spl3_3 | ~spl3_4 | spl3_12),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    $false | (~spl3_3 | ~spl3_4 | spl3_12)),
% 0.22/0.43    inference(subsumption_resolution,[],[f83,f33])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    v1_relat_1(sK0) | ~spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    spl3_3 <=> v1_relat_1(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f83,plain,(
% 0.22/0.43    ~v1_relat_1(sK0) | (~spl3_4 | spl3_12)),
% 0.22/0.43    inference(resolution,[],[f77,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    spl3_4 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    ~v1_relat_1(k7_relat_1(sK0,sK2)) | spl3_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f75])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    spl3_10 | ~spl3_3 | ~spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f62,f59,f31,f65])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    spl3_9 <=> ! [X0] : (k7_relat_1(k7_relat_1(X0,sK2),sK1) = k7_relat_1(X0,sK1) | ~v1_relat_1(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1) | (~spl3_3 | ~spl3_9)),
% 0.22/0.43    inference(resolution,[],[f60,f33])).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(k7_relat_1(X0,sK2),sK1) = k7_relat_1(X0,sK1)) ) | ~spl3_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f59])).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    spl3_9 | ~spl3_2 | ~spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f57,f44,f26,f59])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    spl3_6 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0] : (k7_relat_1(k7_relat_1(X0,sK2),sK1) = k7_relat_1(X0,sK1) | ~v1_relat_1(X0)) ) | (~spl3_2 | ~spl3_6)),
% 0.22/0.43    inference(resolution,[],[f45,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f26])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~v1_relat_1(X2)) ) | ~spl3_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f44])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    spl3_7 | ~spl3_3 | ~spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f47,f40,f31,f50])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | (~spl3_3 | ~spl3_5)),
% 0.22/0.43    inference(resolution,[],[f41,f33])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl3_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f19,f44])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    spl3_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f18,f40])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl3_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f17,f36])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl3_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f14,f31])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    v1_relat_1(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ? [X2,X1] : (k9_relat_1(k7_relat_1(sK0,X2),X1) != k9_relat_1(sK0,X1) & r1_tarski(X1,X2)) => (k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1) & r1_tarski(sK1,sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0] : (? [X1,X2] : (k9_relat_1(k7_relat_1(X0,X2),X1) != k9_relat_1(X0,X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.22/0.43    inference(negated_conjecture,[],[f4])).
% 0.22/0.43  fof(f4,conjecture,(
% 0.22/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(k7_relat_1(X0,X2),X1) = k9_relat_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    spl3_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f15,f26])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    r1_tarski(sK1,sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ~spl3_1),
% 0.22/0.43    inference(avatar_split_clause,[],[f16,f21])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (7438)------------------------------
% 0.22/0.43  % (7438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (7438)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (7438)Memory used [KB]: 10618
% 0.22/0.43  % (7438)Time elapsed: 0.007 s
% 0.22/0.43  % (7438)------------------------------
% 0.22/0.43  % (7438)------------------------------
% 0.22/0.44  % (7432)Success in time 0.077 s
%------------------------------------------------------------------------------
