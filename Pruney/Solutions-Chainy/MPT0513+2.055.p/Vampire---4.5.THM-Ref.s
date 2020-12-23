%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  64 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :  105 ( 137 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f39,f43,f47,f51,f57,f64,f67])).

fof(f67,plain,
    ( spl1_1
    | ~ spl1_9 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl1_1
    | ~ spl1_9 ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_9 ),
    inference(superposition,[],[f23,f63])).

fof(f63,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl1_9
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f23,plain,
    ( k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl1_1
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f64,plain,
    ( spl1_9
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f60,f54,f49,f45,f36,f62])).

fof(f36,plain,
    ( spl1_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f45,plain,
    ( spl1_6
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f49,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ r1_tarski(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f54,plain,
    ( spl1_8
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f60,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f59,f56])).

fof(f56,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f54])).

fof(f59,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f58,f46])).

fof(f46,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f58,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_4
    | ~ spl1_7 ),
    inference(superposition,[],[f50,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_relat_1(X1),X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f57,plain,
    ( spl1_8
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f52,f41,f26,f54])).

fof(f26,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f41,plain,
    ( spl1_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f52,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(superposition,[],[f42,f28])).

fof(f28,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f42,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f51,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f47,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f43,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f39,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f15,f36])).

fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f29,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f24,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f13,f21])).

fof(f13,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).

fof(f11,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (25243)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.44  % (25243)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f24,f29,f39,f43,f47,f51,f57,f64,f67])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    spl1_1 | ~spl1_9),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f66])).
% 0.20/0.44  fof(f66,plain,(
% 0.20/0.44    $false | (spl1_1 | ~spl1_9)),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f65])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_9)),
% 0.20/0.44    inference(superposition,[],[f23,f63])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl1_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f62])).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    spl1_9 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    spl1_1 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    spl1_9 | ~spl1_4 | ~spl1_6 | ~spl1_7 | ~spl1_8),
% 0.20/0.44    inference(avatar_split_clause,[],[f60,f54,f49,f45,f36,f62])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    spl1_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    spl1_6 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    spl1_7 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    spl1_8 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl1_4 | ~spl1_6 | ~spl1_7 | ~spl1_8)),
% 0.20/0.44    inference(subsumption_resolution,[],[f59,f56])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    v1_relat_1(k1_xboole_0) | ~spl1_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f54])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_4 | ~spl1_6 | ~spl1_7)),
% 0.20/0.44    inference(subsumption_resolution,[],[f58,f46])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl1_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f45])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_4 | ~spl1_7)),
% 0.20/0.44    inference(superposition,[],[f50,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f36])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl1_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f49])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    spl1_8 | ~spl1_2 | ~spl1_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f52,f41,f26,f54])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    spl1_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_5)),
% 0.20/0.44    inference(superposition,[],[f42,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f26])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f41])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    spl1_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f19,f49])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    spl1_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f18,f45])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    spl1_5),
% 0.20/0.44    inference(avatar_split_clause,[],[f17,f41])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    spl1_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f15,f36])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    spl1_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f14,f26])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ~spl1_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f13,f21])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,negated_conjecture,(
% 0.20/0.44    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.20/0.44    inference(negated_conjecture,[],[f6])).
% 0.20/0.44  fof(f6,conjecture,(
% 0.20/0.44    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (25243)------------------------------
% 0.20/0.44  % (25243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (25243)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (25243)Memory used [KB]: 10490
% 0.20/0.44  % (25243)Time elapsed: 0.027 s
% 0.20/0.44  % (25243)------------------------------
% 0.20/0.44  % (25243)------------------------------
% 0.20/0.44  % (25236)Success in time 0.09 s
%------------------------------------------------------------------------------
