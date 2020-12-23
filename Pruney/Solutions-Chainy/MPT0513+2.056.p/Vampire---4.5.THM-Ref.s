%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   13 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   87 ( 115 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f30,f34,f38,f44,f50,f54])).

fof(f54,plain,
    ( spl1_1
    | ~ spl1_7 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl1_1
    | ~ spl1_7 ),
    inference(trivial_inequality_removal,[],[f51])).

fof(f51,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl1_1
    | ~ spl1_7 ),
    inference(superposition,[],[f20,f49])).

fof(f49,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl1_7
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f20,plain,
    ( k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl1_1
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f50,plain,
    ( spl1_7
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f46,f41,f36,f32,f48])).

fof(f32,plain,
    ( spl1_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f36,plain,
    ( spl1_5
  <=> ! [X1,X0] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f41,plain,
    ( spl1_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f46,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(subsumption_resolution,[],[f45,f43])).

fof(f43,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f41])).

fof(f45,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f32])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f36])).

fof(f44,plain,
    ( spl1_6
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f39,f28,f23,f41])).

fof(f23,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f28,plain,
    ( spl1_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f39,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(superposition,[],[f29,f25])).

fof(f25,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f29,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f38,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f34,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f30,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f14,f28])).

fof(f14,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f26,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f13,f23])).

fof(f13,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f21,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f12,f18])).

fof(f12,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:19 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.36  ipcrm: permission denied for id (1219166209)
% 0.20/0.36  ipcrm: permission denied for id (1219264516)
% 0.20/0.37  ipcrm: permission denied for id (1218772999)
% 0.20/0.37  ipcrm: permission denied for id (1219362824)
% 0.20/0.37  ipcrm: permission denied for id (1218805769)
% 0.20/0.37  ipcrm: permission denied for id (1219395594)
% 0.20/0.37  ipcrm: permission denied for id (1219428363)
% 0.20/0.37  ipcrm: permission denied for id (1219461132)
% 0.20/0.37  ipcrm: permission denied for id (1218838541)
% 0.20/0.38  ipcrm: permission denied for id (1219526670)
% 0.20/0.38  ipcrm: permission denied for id (1219559439)
% 0.20/0.38  ipcrm: permission denied for id (1219624977)
% 0.20/0.38  ipcrm: permission denied for id (1219690515)
% 0.20/0.38  ipcrm: permission denied for id (1219756053)
% 0.20/0.39  ipcrm: permission denied for id (1219854360)
% 0.20/0.39  ipcrm: permission denied for id (1219887129)
% 0.20/0.39  ipcrm: permission denied for id (1219985436)
% 0.20/0.39  ipcrm: permission denied for id (1220050974)
% 0.20/0.40  ipcrm: permission denied for id (1220116512)
% 0.20/0.40  ipcrm: permission denied for id (1220280357)
% 0.20/0.40  ipcrm: permission denied for id (1220313126)
% 0.20/0.41  ipcrm: permission denied for id (1220378664)
% 0.20/0.41  ipcrm: permission denied for id (1220411433)
% 0.20/0.41  ipcrm: permission denied for id (1220444202)
% 0.20/0.41  ipcrm: permission denied for id (1220476971)
% 0.20/0.41  ipcrm: permission denied for id (1220509740)
% 0.20/0.41  ipcrm: permission denied for id (1220542509)
% 0.20/0.41  ipcrm: permission denied for id (1220575278)
% 0.20/0.41  ipcrm: permission denied for id (1220608047)
% 0.20/0.42  ipcrm: permission denied for id (1220640816)
% 0.20/0.42  ipcrm: permission denied for id (1220706354)
% 0.20/0.42  ipcrm: permission denied for id (1220739123)
% 0.20/0.42  ipcrm: permission denied for id (1220771892)
% 0.20/0.42  ipcrm: permission denied for id (1220804661)
% 0.20/0.42  ipcrm: permission denied for id (1220837430)
% 0.20/0.42  ipcrm: permission denied for id (1220870199)
% 0.20/0.42  ipcrm: permission denied for id (1219002424)
% 0.20/0.43  ipcrm: permission denied for id (1220935738)
% 0.20/0.43  ipcrm: permission denied for id (1220968507)
% 0.20/0.43  ipcrm: permission denied for id (1221034045)
% 0.20/0.43  ipcrm: permission denied for id (1221066814)
% 0.20/0.43  ipcrm: permission denied for id (1221132352)
% 0.20/0.44  ipcrm: permission denied for id (1221165121)
% 0.20/0.44  ipcrm: permission denied for id (1221230659)
% 0.20/0.44  ipcrm: permission denied for id (1221263428)
% 0.20/0.44  ipcrm: permission denied for id (1221296197)
% 0.20/0.44  ipcrm: permission denied for id (1221328966)
% 0.20/0.44  ipcrm: permission denied for id (1221394504)
% 0.20/0.44  ipcrm: permission denied for id (1221427273)
% 0.20/0.45  ipcrm: permission denied for id (1221460042)
% 0.20/0.45  ipcrm: permission denied for id (1221525580)
% 0.20/0.45  ipcrm: permission denied for id (1221558349)
% 0.20/0.45  ipcrm: permission denied for id (1221591118)
% 0.20/0.45  ipcrm: permission denied for id (1221623887)
% 0.20/0.46  ipcrm: permission denied for id (1221754963)
% 0.20/0.46  ipcrm: permission denied for id (1221787732)
% 0.20/0.46  ipcrm: permission denied for id (1221820501)
% 0.20/0.46  ipcrm: permission denied for id (1221853270)
% 0.20/0.46  ipcrm: permission denied for id (1221886039)
% 0.20/0.46  ipcrm: permission denied for id (1221951576)
% 0.20/0.46  ipcrm: permission denied for id (1221984345)
% 0.20/0.47  ipcrm: permission denied for id (1222115421)
% 0.20/0.47  ipcrm: permission denied for id (1222180959)
% 0.20/0.47  ipcrm: permission denied for id (1222213728)
% 0.20/0.47  ipcrm: permission denied for id (1222246497)
% 0.20/0.48  ipcrm: permission denied for id (1222377573)
% 0.20/0.48  ipcrm: permission denied for id (1222410342)
% 0.20/0.48  ipcrm: permission denied for id (1222475880)
% 0.20/0.48  ipcrm: permission denied for id (1222508649)
% 0.20/0.49  ipcrm: permission denied for id (1222606956)
% 0.20/0.49  ipcrm: permission denied for id (1222639725)
% 0.20/0.49  ipcrm: permission denied for id (1219068014)
% 0.20/0.49  ipcrm: permission denied for id (1222705264)
% 0.20/0.50  ipcrm: permission denied for id (1222836340)
% 0.20/0.50  ipcrm: permission denied for id (1222934647)
% 0.20/0.50  ipcrm: permission denied for id (1222967416)
% 0.20/0.50  ipcrm: permission denied for id (1219100793)
% 0.20/0.51  ipcrm: permission denied for id (1223098493)
% 0.20/0.56  % (11148)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.57  % (11147)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.57  % (11149)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.57  % (11147)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f21,f26,f30,f34,f38,f44,f50,f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    spl1_1 | ~spl1_7),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    $false | (spl1_1 | ~spl1_7)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | (spl1_1 | ~spl1_7)),
% 0.20/0.57    inference(superposition,[],[f20,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl1_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    spl1_7 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.20/0.57    inference(avatar_component_clause,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    spl1_1 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    spl1_7 | ~spl1_4 | ~spl1_5 | ~spl1_6),
% 0.20/0.57    inference(avatar_split_clause,[],[f46,f41,f36,f32,f48])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    spl1_4 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    spl1_5 <=> ! [X1,X0] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    spl1_6 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl1_4 | ~spl1_5 | ~spl1_6)),
% 0.20/0.57    inference(subsumption_resolution,[],[f45,f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    v1_relat_1(k1_xboole_0) | ~spl1_6),
% 0.20/0.57    inference(avatar_component_clause,[],[f41])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl1_4 | ~spl1_5)),
% 0.20/0.57    inference(resolution,[],[f37,f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl1_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f32])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) ) | ~spl1_5),
% 0.20/0.57    inference(avatar_component_clause,[],[f36])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    spl1_6 | ~spl1_2 | ~spl1_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f39,f28,f23,f41])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    spl1_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_3)),
% 0.20/0.57    inference(superposition,[],[f29,f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.20/0.57    inference(avatar_component_clause,[],[f23])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f28])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    spl1_5),
% 0.20/0.57    inference(avatar_split_clause,[],[f16,f36])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    spl1_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f15,f32])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,plain,(
% 0.20/0.57    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.57    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    spl1_3),
% 0.20/0.57    inference(avatar_split_clause,[],[f14,f28])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    spl1_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f13,f23])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ~spl1_1),
% 0.20/0.57    inference(avatar_split_clause,[],[f12,f18])).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.20/0.57    inference(cnf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,plain,(
% 0.20/0.57    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.20/0.57  fof(f10,plain,(
% 0.20/0.57    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0)),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f7,plain,(
% 0.20/0.57    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,negated_conjecture,(
% 0.20/0.57    ~! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.20/0.57    inference(negated_conjecture,[],[f5])).
% 0.20/0.57  fof(f5,conjecture,(
% 0.20/0.57    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (11147)------------------------------
% 0.20/0.57  % (11147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (11147)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (11147)Memory used [KB]: 10490
% 0.20/0.57  % (11147)Time elapsed: 0.004 s
% 0.20/0.57  % (11147)------------------------------
% 0.20/0.57  % (11147)------------------------------
% 0.68/0.57  % (11008)Success in time 0.22 s
%------------------------------------------------------------------------------
