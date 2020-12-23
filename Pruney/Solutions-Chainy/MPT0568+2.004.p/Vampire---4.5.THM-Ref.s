%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:10 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   86 (  98 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f76,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f47,f61,f66,f74])).

% (25529)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f74,plain,
    ( spl1_4
    | ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl1_4
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f46,f20,f60,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

% (25550)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f60,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl1_6
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f20,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl1_4
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f66,plain,
    ( ~ spl1_1
    | spl1_5 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl1_1
    | spl1_5 ),
    inference(subsumption_resolution,[],[f63,f31])).

fof(f31,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl1_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f63,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_5 ),
    inference(resolution,[],[f57,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f57,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f61,plain,
    ( ~ spl1_5
    | spl1_6
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f48,f34,f59,f55])).

fof(f34,plain,
    ( spl1_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f48,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_2 ),
    inference(superposition,[],[f22,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f47,plain,(
    ~ spl1_4 ),
    inference(avatar_split_clause,[],[f16,f44])).

fof(f16,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).

fof(f12,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f37,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f32,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:19:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (25527)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (25526)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.54  % (25527)Refutation found. Thanks to Tanya!
% 1.46/0.54  % SZS status Theorem for theBenchmark
% 1.46/0.54  % SZS output start Proof for theBenchmark
% 1.46/0.54  fof(f76,plain,(
% 1.46/0.54    $false),
% 1.46/0.54    inference(avatar_sat_refutation,[],[f32,f37,f47,f61,f66,f74])).
% 1.46/0.54  % (25529)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.46/0.54  fof(f74,plain,(
% 1.46/0.54    spl1_4 | ~spl1_6),
% 1.46/0.54    inference(avatar_contradiction_clause,[],[f69])).
% 1.46/0.54  fof(f69,plain,(
% 1.46/0.54    $false | (spl1_4 | ~spl1_6)),
% 1.46/0.54    inference(unit_resulting_resolution,[],[f46,f20,f60,f25])).
% 1.46/0.54  fof(f25,plain,(
% 1.46/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.46/0.54    inference(cnf_transformation,[],[f15])).
% 1.46/0.54  fof(f15,plain,(
% 1.46/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.54    inference(flattening,[],[f14])).
% 1.46/0.54  fof(f14,plain,(
% 1.46/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.54    inference(nnf_transformation,[],[f2])).
% 1.46/0.55  % (25550)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.46/0.55  fof(f2,axiom,(
% 1.46/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.55  fof(f60,plain,(
% 1.46/0.55    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_6),
% 1.46/0.55    inference(avatar_component_clause,[],[f59])).
% 1.46/0.55  fof(f59,plain,(
% 1.46/0.55    spl1_6 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.46/0.55  fof(f20,plain,(
% 1.46/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f3])).
% 1.46/0.55  fof(f3,axiom,(
% 1.46/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.46/0.55  fof(f46,plain,(
% 1.46/0.55    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_4),
% 1.46/0.55    inference(avatar_component_clause,[],[f44])).
% 1.46/0.55  fof(f44,plain,(
% 1.46/0.55    spl1_4 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.46/0.55  fof(f66,plain,(
% 1.46/0.55    ~spl1_1 | spl1_5),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f65])).
% 1.46/0.55  fof(f65,plain,(
% 1.46/0.55    $false | (~spl1_1 | spl1_5)),
% 1.46/0.55    inference(subsumption_resolution,[],[f63,f31])).
% 1.46/0.55  fof(f31,plain,(
% 1.46/0.55    v1_xboole_0(k1_xboole_0) | ~spl1_1),
% 1.46/0.55    inference(avatar_component_clause,[],[f29])).
% 1.46/0.55  fof(f29,plain,(
% 1.46/0.55    spl1_1 <=> v1_xboole_0(k1_xboole_0)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.46/0.55  fof(f63,plain,(
% 1.46/0.55    ~v1_xboole_0(k1_xboole_0) | spl1_5),
% 1.46/0.55    inference(resolution,[],[f57,f21])).
% 1.46/0.55  fof(f21,plain,(
% 1.46/0.55    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f10])).
% 1.46/0.55  fof(f10,plain,(
% 1.46/0.55    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.46/0.55    inference(ennf_transformation,[],[f4])).
% 1.46/0.55  fof(f4,axiom,(
% 1.46/0.55    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.46/0.55  fof(f57,plain,(
% 1.46/0.55    ~v1_relat_1(k1_xboole_0) | spl1_5),
% 1.46/0.55    inference(avatar_component_clause,[],[f55])).
% 1.46/0.55  fof(f55,plain,(
% 1.46/0.55    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.46/0.55  fof(f61,plain,(
% 1.46/0.55    ~spl1_5 | spl1_6 | ~spl1_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f48,f34,f59,f55])).
% 1.46/0.55  fof(f34,plain,(
% 1.46/0.55    spl1_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.46/0.55  fof(f48,plain,(
% 1.46/0.55    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl1_2),
% 1.46/0.55    inference(superposition,[],[f22,f36])).
% 1.46/0.55  fof(f36,plain,(
% 1.46/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_2),
% 1.46/0.55    inference(avatar_component_clause,[],[f34])).
% 1.46/0.55  fof(f22,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f11])).
% 1.46/0.55  fof(f11,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f5])).
% 1.46/0.55  fof(f5,axiom,(
% 1.46/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.46/0.55  fof(f47,plain,(
% 1.46/0.55    ~spl1_4),
% 1.46/0.55    inference(avatar_split_clause,[],[f16,f44])).
% 1.46/0.55  fof(f16,plain,(
% 1.46/0.55    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.46/0.55    inference(cnf_transformation,[],[f13])).
% 1.46/0.55  fof(f13,plain,(
% 1.46/0.55    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f12])).
% 1.46/0.55  fof(f12,plain,(
% 1.46/0.55    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f9,plain,(
% 1.46/0.55    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.46/0.55    inference(ennf_transformation,[],[f8])).
% 1.46/0.55  fof(f8,negated_conjecture,(
% 1.46/0.55    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.46/0.55    inference(negated_conjecture,[],[f7])).
% 1.46/0.55  fof(f7,conjecture,(
% 1.46/0.55    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 1.46/0.55  fof(f37,plain,(
% 1.46/0.55    spl1_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f18,f34])).
% 1.46/0.55  fof(f18,plain,(
% 1.46/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.55    inference(cnf_transformation,[],[f6])).
% 1.46/0.55  fof(f6,axiom,(
% 1.46/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.46/0.55  fof(f32,plain,(
% 1.46/0.55    spl1_1),
% 1.46/0.55    inference(avatar_split_clause,[],[f17,f29])).
% 1.46/0.55  fof(f17,plain,(
% 1.46/0.55    v1_xboole_0(k1_xboole_0)),
% 1.46/0.55    inference(cnf_transformation,[],[f1])).
% 1.46/0.55  fof(f1,axiom,(
% 1.46/0.55    v1_xboole_0(k1_xboole_0)),
% 1.46/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.46/0.55  % SZS output end Proof for theBenchmark
% 1.46/0.55  % (25527)------------------------------
% 1.46/0.55  % (25527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (25527)Termination reason: Refutation
% 1.46/0.55  
% 1.46/0.55  % (25527)Memory used [KB]: 6140
% 1.46/0.55  % (25527)Time elapsed: 0.099 s
% 1.46/0.55  % (25527)------------------------------
% 1.46/0.55  % (25527)------------------------------
% 1.46/0.55  % (25524)Success in time 0.19 s
%------------------------------------------------------------------------------
