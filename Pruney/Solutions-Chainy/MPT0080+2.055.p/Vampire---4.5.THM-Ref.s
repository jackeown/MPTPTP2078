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
% DateTime   : Thu Dec  3 12:31:06 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   59 (  87 expanded)
%              Number of leaves         :   16 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :  155 ( 241 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f37,f41,f49,f53,f57,f126,f142,f171,f182])).

fof(f182,plain,
    ( ~ spl3_4
    | spl3_17
    | ~ spl3_20
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl3_4
    | spl3_17
    | ~ spl3_20
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f180,f40])).

fof(f40,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f180,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | spl3_17
    | ~ spl3_20
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f173,f125])).

fof(f125,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_17
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f173,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_20
    | ~ spl3_24 ),
    inference(resolution,[],[f170,f141])).

fof(f141,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_20
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl3_24
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f171,plain,
    ( spl3_24
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f167,f55,f29,f169])).

fof(f29,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f55,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( k1_xboole_0 = X0
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f167,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f56,f31])).

fof(f31,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f56,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f142,plain,
    ( spl3_20
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f129,f51,f34,f139])).

fof(f34,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f51,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f129,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f52,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | r1_tarski(k4_xboole_0(X0,X1),X2) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f126,plain,
    ( ~ spl3_17
    | spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f120,f47,f24,f123])).

fof(f24,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f47,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f120,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f57,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f22,f55])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f53,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f49,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f41,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f29])).

fof(f16,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f24])).

fof(f17,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (1224933376)
% 0.14/0.37  ipcrm: permission denied for id (1225752577)
% 0.14/0.37  ipcrm: permission denied for id (1224998918)
% 0.14/0.37  ipcrm: permission denied for id (1225916423)
% 0.14/0.38  ipcrm: permission denied for id (1226014730)
% 0.14/0.38  ipcrm: permission denied for id (1226047499)
% 0.14/0.39  ipcrm: permission denied for id (1226276882)
% 0.14/0.39  ipcrm: permission denied for id (1225064468)
% 0.14/0.39  ipcrm: permission denied for id (1226342421)
% 0.14/0.39  ipcrm: permission denied for id (1225097238)
% 0.14/0.40  ipcrm: permission denied for id (1226440729)
% 0.22/0.40  ipcrm: permission denied for id (1226571805)
% 0.22/0.40  ipcrm: permission denied for id (1226670112)
% 0.22/0.41  ipcrm: permission denied for id (1225162786)
% 0.22/0.41  ipcrm: permission denied for id (1226801189)
% 0.22/0.41  ipcrm: permission denied for id (1226866727)
% 0.22/0.42  ipcrm: permission denied for id (1226965034)
% 0.22/0.42  ipcrm: permission denied for id (1227030572)
% 0.22/0.42  ipcrm: permission denied for id (1227063341)
% 0.22/0.42  ipcrm: permission denied for id (1227096110)
% 0.22/0.42  ipcrm: permission denied for id (1227161648)
% 0.22/0.43  ipcrm: permission denied for id (1225228337)
% 0.22/0.43  ipcrm: permission denied for id (1227292725)
% 0.22/0.43  ipcrm: permission denied for id (1227325494)
% 0.22/0.43  ipcrm: permission denied for id (1227358263)
% 0.22/0.43  ipcrm: permission denied for id (1227391032)
% 0.22/0.44  ipcrm: permission denied for id (1227456570)
% 0.22/0.44  ipcrm: permission denied for id (1227489339)
% 0.22/0.44  ipcrm: permission denied for id (1227522108)
% 0.22/0.44  ipcrm: permission denied for id (1227587646)
% 0.22/0.45  ipcrm: permission denied for id (1227685952)
% 0.22/0.45  ipcrm: permission denied for id (1227718721)
% 0.22/0.45  ipcrm: permission denied for id (1227751490)
% 0.22/0.45  ipcrm: permission denied for id (1227882566)
% 0.22/0.45  ipcrm: permission denied for id (1227915335)
% 0.22/0.46  ipcrm: permission denied for id (1227948104)
% 0.22/0.46  ipcrm: permission denied for id (1227980873)
% 0.22/0.46  ipcrm: permission denied for id (1225261131)
% 0.22/0.46  ipcrm: permission denied for id (1228111950)
% 0.22/0.47  ipcrm: permission denied for id (1225293904)
% 0.22/0.47  ipcrm: permission denied for id (1225359442)
% 0.22/0.47  ipcrm: permission denied for id (1228275796)
% 0.22/0.47  ipcrm: permission denied for id (1228341334)
% 0.22/0.48  ipcrm: permission denied for id (1228374103)
% 0.22/0.48  ipcrm: permission denied for id (1228439641)
% 0.22/0.48  ipcrm: permission denied for id (1228472410)
% 0.22/0.48  ipcrm: permission denied for id (1228505179)
% 0.22/0.48  ipcrm: permission denied for id (1228537948)
% 0.22/0.49  ipcrm: permission denied for id (1225457758)
% 0.22/0.49  ipcrm: permission denied for id (1228603487)
% 0.22/0.49  ipcrm: permission denied for id (1228636256)
% 0.22/0.49  ipcrm: permission denied for id (1225490530)
% 0.22/0.49  ipcrm: permission denied for id (1228701795)
% 0.22/0.49  ipcrm: permission denied for id (1228734564)
% 0.22/0.50  ipcrm: permission denied for id (1228800102)
% 0.22/0.50  ipcrm: permission denied for id (1225556071)
% 0.22/0.50  ipcrm: permission denied for id (1228832872)
% 0.22/0.50  ipcrm: permission denied for id (1228865641)
% 0.22/0.50  ipcrm: permission denied for id (1228898410)
% 0.22/0.50  ipcrm: permission denied for id (1228931179)
% 0.22/0.50  ipcrm: permission denied for id (1228963948)
% 0.22/0.51  ipcrm: permission denied for id (1229029486)
% 0.22/0.51  ipcrm: permission denied for id (1229062255)
% 0.22/0.51  ipcrm: permission denied for id (1229095024)
% 0.22/0.51  ipcrm: permission denied for id (1229127793)
% 0.22/0.51  ipcrm: permission denied for id (1225621619)
% 0.22/0.51  ipcrm: permission denied for id (1229193332)
% 0.22/0.52  ipcrm: permission denied for id (1229226101)
% 0.22/0.52  ipcrm: permission denied for id (1225654390)
% 0.22/0.52  ipcrm: permission denied for id (1229291640)
% 0.22/0.52  ipcrm: permission denied for id (1229324409)
% 0.22/0.52  ipcrm: permission denied for id (1229357178)
% 0.22/0.53  ipcrm: permission denied for id (1229488254)
% 0.22/0.59  % (21629)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.76/0.59  % (21630)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.76/0.60  % (21628)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.76/0.60  % (21628)Refutation found. Thanks to Tanya!
% 0.76/0.60  % SZS status Theorem for theBenchmark
% 0.76/0.60  % SZS output start Proof for theBenchmark
% 0.76/0.60  fof(f183,plain,(
% 0.76/0.60    $false),
% 0.76/0.60    inference(avatar_sat_refutation,[],[f27,f32,f37,f41,f49,f53,f57,f126,f142,f171,f182])).
% 0.76/0.60  fof(f182,plain,(
% 0.76/0.60    ~spl3_4 | spl3_17 | ~spl3_20 | ~spl3_24),
% 0.76/0.60    inference(avatar_contradiction_clause,[],[f181])).
% 0.76/0.60  fof(f181,plain,(
% 0.76/0.60    $false | (~spl3_4 | spl3_17 | ~spl3_20 | ~spl3_24)),
% 0.76/0.60    inference(subsumption_resolution,[],[f180,f40])).
% 0.76/0.60  fof(f40,plain,(
% 0.76/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_4),
% 0.76/0.60    inference(avatar_component_clause,[],[f39])).
% 0.76/0.60  fof(f39,plain,(
% 0.76/0.60    spl3_4 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.76/0.60  fof(f180,plain,(
% 0.76/0.60    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | (spl3_17 | ~spl3_20 | ~spl3_24)),
% 0.76/0.60    inference(subsumption_resolution,[],[f173,f125])).
% 0.76/0.60  fof(f125,plain,(
% 0.76/0.60    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_17),
% 0.76/0.60    inference(avatar_component_clause,[],[f123])).
% 0.76/0.60  fof(f123,plain,(
% 0.76/0.60    spl3_17 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.76/0.60  fof(f173,plain,(
% 0.76/0.60    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | (~spl3_20 | ~spl3_24)),
% 0.76/0.60    inference(resolution,[],[f170,f141])).
% 0.76/0.60  fof(f141,plain,(
% 0.76/0.60    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl3_20),
% 0.76/0.60    inference(avatar_component_clause,[],[f139])).
% 0.76/0.60  fof(f139,plain,(
% 0.76/0.60    spl3_20 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.76/0.60  fof(f170,plain,(
% 0.76/0.60    ( ! [X0] : (~r1_tarski(X0,sK2) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK0)) ) | ~spl3_24),
% 0.76/0.60    inference(avatar_component_clause,[],[f169])).
% 0.76/0.60  fof(f169,plain,(
% 0.76/0.60    spl3_24 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,sK2) | ~r1_tarski(X0,sK0))),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.76/0.60  fof(f171,plain,(
% 0.76/0.60    spl3_24 | ~spl3_2 | ~spl3_8),
% 0.76/0.60    inference(avatar_split_clause,[],[f167,f55,f29,f169])).
% 0.76/0.60  fof(f29,plain,(
% 0.76/0.60    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.76/0.60  fof(f55,plain,(
% 0.76/0.60    spl3_8 <=> ! [X1,X0,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.76/0.60  fof(f167,plain,(
% 0.76/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,sK2) | ~r1_tarski(X0,sK0)) ) | (~spl3_2 | ~spl3_8)),
% 0.76/0.60    inference(resolution,[],[f56,f31])).
% 0.76/0.60  fof(f31,plain,(
% 0.76/0.60    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.76/0.60    inference(avatar_component_clause,[],[f29])).
% 0.76/0.60  fof(f56,plain,(
% 0.76/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.76/0.60    inference(avatar_component_clause,[],[f55])).
% 0.76/0.60  fof(f142,plain,(
% 0.76/0.60    spl3_20 | ~spl3_3 | ~spl3_7),
% 0.76/0.60    inference(avatar_split_clause,[],[f129,f51,f34,f139])).
% 0.76/0.60  fof(f34,plain,(
% 0.76/0.60    spl3_3 <=> r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.76/0.60  fof(f51,plain,(
% 0.76/0.60    spl3_7 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.76/0.60  fof(f129,plain,(
% 0.76/0.60    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | (~spl3_3 | ~spl3_7)),
% 0.76/0.60    inference(resolution,[],[f52,f36])).
% 0.76/0.60  fof(f36,plain,(
% 0.76/0.60    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.76/0.60    inference(avatar_component_clause,[],[f34])).
% 0.76/0.60  fof(f52,plain,(
% 0.76/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) ) | ~spl3_7),
% 0.76/0.60    inference(avatar_component_clause,[],[f51])).
% 0.76/0.60  fof(f126,plain,(
% 0.76/0.60    ~spl3_17 | spl3_1 | ~spl3_6),
% 0.76/0.60    inference(avatar_split_clause,[],[f120,f47,f24,f123])).
% 0.76/0.60  fof(f24,plain,(
% 0.76/0.60    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.76/0.60  fof(f47,plain,(
% 0.76/0.60    spl3_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.76/0.60  fof(f120,plain,(
% 0.76/0.60    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_1 | ~spl3_6)),
% 0.76/0.60    inference(resolution,[],[f48,f26])).
% 0.76/0.60  fof(f26,plain,(
% 0.76/0.60    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.76/0.60    inference(avatar_component_clause,[],[f24])).
% 0.76/0.60  fof(f48,plain,(
% 0.76/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl3_6),
% 0.76/0.60    inference(avatar_component_clause,[],[f47])).
% 0.76/0.60  fof(f57,plain,(
% 0.76/0.60    spl3_8),
% 0.76/0.60    inference(avatar_split_clause,[],[f22,f55])).
% 0.76/0.60  fof(f22,plain,(
% 0.76/0.60    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.76/0.60    inference(cnf_transformation,[],[f11])).
% 0.76/0.60  fof(f11,plain,(
% 0.76/0.60    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.76/0.60    inference(flattening,[],[f10])).
% 0.76/0.60  fof(f10,plain,(
% 0.76/0.60    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.76/0.60    inference(ennf_transformation,[],[f4])).
% 0.76/0.60  fof(f4,axiom,(
% 0.76/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.76/0.60  fof(f53,plain,(
% 0.76/0.60    spl3_7),
% 0.76/0.60    inference(avatar_split_clause,[],[f21,f51])).
% 0.76/0.60  fof(f21,plain,(
% 0.76/0.60    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.76/0.60    inference(cnf_transformation,[],[f9])).
% 0.76/0.60  fof(f9,plain,(
% 0.76/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.76/0.60    inference(ennf_transformation,[],[f3])).
% 0.76/0.60  fof(f3,axiom,(
% 0.76/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.76/0.60  fof(f49,plain,(
% 0.76/0.60    spl3_6),
% 0.76/0.60    inference(avatar_split_clause,[],[f19,f47])).
% 0.76/0.60  fof(f19,plain,(
% 0.76/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.76/0.60    inference(cnf_transformation,[],[f14])).
% 0.76/0.60  fof(f14,plain,(
% 0.76/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.76/0.60    inference(nnf_transformation,[],[f1])).
% 0.76/0.60  fof(f1,axiom,(
% 0.76/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.76/0.60  fof(f41,plain,(
% 0.76/0.60    spl3_4),
% 0.76/0.60    inference(avatar_split_clause,[],[f18,f39])).
% 0.76/0.60  fof(f18,plain,(
% 0.76/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.76/0.60    inference(cnf_transformation,[],[f2])).
% 0.76/0.60  fof(f2,axiom,(
% 0.76/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.76/0.60  fof(f37,plain,(
% 0.76/0.60    spl3_3),
% 0.76/0.60    inference(avatar_split_clause,[],[f15,f34])).
% 0.76/0.60  fof(f15,plain,(
% 0.76/0.60    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.76/0.60    inference(cnf_transformation,[],[f13])).
% 0.76/0.60  fof(f13,plain,(
% 0.76/0.60    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.76/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.76/0.60  fof(f12,plain,(
% 0.76/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.76/0.60    introduced(choice_axiom,[])).
% 0.76/0.60  fof(f8,plain,(
% 0.76/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.76/0.60    inference(flattening,[],[f7])).
% 0.76/0.60  fof(f7,plain,(
% 0.76/0.60    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.76/0.60    inference(ennf_transformation,[],[f6])).
% 0.76/0.60  fof(f6,negated_conjecture,(
% 0.76/0.60    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.76/0.60    inference(negated_conjecture,[],[f5])).
% 0.76/0.60  fof(f5,conjecture,(
% 0.76/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.76/0.60  fof(f32,plain,(
% 0.76/0.60    spl3_2),
% 0.76/0.60    inference(avatar_split_clause,[],[f16,f29])).
% 0.76/0.60  fof(f16,plain,(
% 0.76/0.60    r1_xboole_0(sK0,sK2)),
% 0.76/0.60    inference(cnf_transformation,[],[f13])).
% 0.76/0.60  fof(f27,plain,(
% 0.76/0.60    ~spl3_1),
% 0.76/0.60    inference(avatar_split_clause,[],[f17,f24])).
% 0.76/0.60  fof(f17,plain,(
% 0.76/0.60    ~r1_tarski(sK0,sK1)),
% 0.76/0.60    inference(cnf_transformation,[],[f13])).
% 0.76/0.60  % SZS output end Proof for theBenchmark
% 0.76/0.60  % (21628)------------------------------
% 0.76/0.60  % (21628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.76/0.60  % (21628)Termination reason: Refutation
% 0.76/0.60  
% 0.76/0.60  % (21628)Memory used [KB]: 10618
% 0.76/0.60  % (21628)Time elapsed: 0.008 s
% 0.76/0.60  % (21628)------------------------------
% 0.76/0.60  % (21628)------------------------------
% 0.76/0.61  % (21444)Success in time 0.249 s
%------------------------------------------------------------------------------
