%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 104 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f43,f53,f55])).

fof(f55,plain,(
    spl1_4 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl1_4 ),
    inference(subsumption_resolution,[],[f35,f38])).

fof(f38,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f19,f15])).

fof(f15,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f35,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl1_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f53,plain,(
    spl1_3 ),
    inference(avatar_contradiction_clause,[],[f52])).

fof(f52,plain,
    ( $false
    | spl1_3 ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl1_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl1_3
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f47,plain,(
    ! [X2] : v5_relat_1(k1_xboole_0,X2) ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f18,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f46,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | v5_relat_1(k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f45,f17])).

fof(f17,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f45,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),X2)
      | v5_relat_1(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f22,f38])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f43,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | spl1_2 ),
    inference(subsumption_resolution,[],[f29,f37])).

fof(f37,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f20,f15])).

fof(f20,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl1_2
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f41,plain,(
    spl1_1 ),
    inference(avatar_contradiction_clause,[],[f40])).

fof(f40,plain,
    ( $false
    | spl1_1 ),
    inference(subsumption_resolution,[],[f39,f14])).

fof(f14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f39,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl1_1 ),
    inference(resolution,[],[f21,f26])).

fof(f26,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_1
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f21,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v5_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).

fof(f36,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f13,f34,f31,f28,f25])).

fof(f13,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (6378)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.43  % (6383)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (6380)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (6378)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f36,f41,f43,f53,f55])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl1_4),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    $false | spl1_4),
% 0.21/0.43    inference(subsumption_resolution,[],[f35,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(superposition,[],[f19,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ~v1_relat_1(k1_xboole_0) | spl1_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl1_3),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    $false | spl1_3),
% 0.21/0.43    inference(resolution,[],[f47,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ~v5_relat_1(k1_xboole_0,sK0) | spl1_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl1_3 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X2] : (v5_relat_1(k1_xboole_0,X2)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f46,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X2] : (~r1_tarski(k1_xboole_0,X2) | v5_relat_1(k1_xboole_0,X2)) )),
% 0.21/0.43    inference(forward_demodulation,[],[f45,f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ( ! [X2] : (~r1_tarski(k2_relat_1(k1_xboole_0),X2) | v5_relat_1(k1_xboole_0,X2)) )),
% 0.21/0.43    inference(resolution,[],[f22,f38])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl1_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    $false | spl1_2),
% 0.21/0.43    inference(subsumption_resolution,[],[f29,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    v1_funct_1(k1_xboole_0)),
% 0.21/0.43    inference(superposition,[],[f20,f15])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ~v1_funct_1(k1_xboole_0) | spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f28])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    spl1_2 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl1_1),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f40])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    $false | spl1_1),
% 0.21/0.43    inference(subsumption_resolution,[],[f39,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ~v1_xboole_0(k1_xboole_0) | spl1_1),
% 0.21/0.43    inference(resolution,[],[f21,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ~v5_ordinal1(k1_xboole_0) | spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    spl1_1 <=> v5_ordinal1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0] : (v5_ordinal1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) => v5_ordinal1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_ordinal1)).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ~spl1_1 | ~spl1_2 | ~spl1_3 | ~spl1_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f13,f34,f31,f28,f25])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (6378)------------------------------
% 0.21/0.43  % (6378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (6378)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (6378)Memory used [KB]: 10490
% 0.21/0.43  % (6378)Time elapsed: 0.005 s
% 0.21/0.43  % (6378)------------------------------
% 0.21/0.43  % (6378)------------------------------
% 0.21/0.43  % (6374)Success in time 0.077 s
%------------------------------------------------------------------------------
