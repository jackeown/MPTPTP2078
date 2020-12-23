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
% DateTime   : Thu Dec  3 12:42:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 (  66 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :  108 ( 148 expanded)
%              Number of equality atoms :   22 (  34 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f45,f49,f61,f75,f83,f98,f103])).

fof(f103,plain,
    ( ~ spl2_4
    | ~ spl2_8
    | ~ spl2_12
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_12
    | spl2_13 ),
    inference(subsumption_resolution,[],[f91,f99])).

fof(f99,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_8
    | spl2_13 ),
    inference(unit_resulting_resolution,[],[f97,f60])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f97,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(sK0))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_13
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f91,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f82,f44])).

fof(f44,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f82,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_12
  <=> r1_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f98,plain,
    ( ~ spl2_13
    | spl2_2
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f86,f73,f34,f95])).

fof(f34,plain,
    ( spl2_2
  <=> sK1 = k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f73,plain,
    ( spl2_11
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

% (25999)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% (26001)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f86,plain,
    ( sK1 != k4_xboole_0(sK1,k1_tarski(sK0))
    | spl2_2
    | ~ spl2_11 ),
    inference(superposition,[],[f36,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f73])).

fof(f36,plain,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f83,plain,
    ( spl2_12
    | spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f66,f47,f29,f80])).

fof(f29,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

% (26003)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f66,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | spl2_1
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f31,f48])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f31,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f75,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f23,f73])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f37,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & ~ r2_hidden(X0,X1) )
   => ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f29])).

fof(f17,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (26000)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (26002)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (26000)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (26008)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f32,f37,f45,f49,f61,f75,f83,f98,f103])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ~spl2_4 | ~spl2_8 | ~spl2_12 | spl2_13),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    $false | (~spl2_4 | ~spl2_8 | ~spl2_12 | spl2_13)),
% 0.22/0.50    inference(subsumption_resolution,[],[f91,f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ~r1_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_8 | spl2_13)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f97,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl2_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    sK1 != k4_xboole_0(sK1,k1_tarski(sK0)) | spl2_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl2_13 <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    r1_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_4 | ~spl2_12)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f82,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl2_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    spl2_4 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    r1_xboole_0(k1_tarski(sK0),sK1) | ~spl2_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl2_12 <=> r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~spl2_13 | spl2_2 | ~spl2_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f86,f73,f34,f95])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    spl2_2 <=> sK1 = k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl2_11 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.50  % (25999)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (26001)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    sK1 != k4_xboole_0(sK1,k1_tarski(sK0)) | (spl2_2 | ~spl2_11)),
% 0.22/0.50    inference(superposition,[],[f36,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl2_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f73])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl2_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f34])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl2_12 | spl2_1 | ~spl2_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f66,f47,f29,f80])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    spl2_5 <=> ! [X1,X0] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.50  % (26003)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    r1_xboole_0(k1_tarski(sK0),sK1) | (spl2_1 | ~spl2_5)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f31,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f47])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ~r2_hidden(sK0,sK1) | spl2_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f29])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl2_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f73])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl2_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f59])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f24,f47])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    spl2_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f25,f43])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ~spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f34])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1)) => (sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.22/0.51    inference(negated_conjecture,[],[f9])).
% 0.22/0.51  fof(f9,conjecture,(
% 0.22/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f29])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (26000)------------------------------
% 0.22/0.51  % (26000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26000)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (26000)Memory used [KB]: 6140
% 0.22/0.51  % (26000)Time elapsed: 0.067 s
% 0.22/0.51  % (26000)------------------------------
% 0.22/0.51  % (26000)------------------------------
% 0.22/0.51  % (26010)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (25994)Success in time 0.144 s
%------------------------------------------------------------------------------
