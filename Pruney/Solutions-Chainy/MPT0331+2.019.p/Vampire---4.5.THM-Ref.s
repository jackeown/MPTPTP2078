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
% DateTime   : Thu Dec  3 12:43:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  66 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :  113 ( 172 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f87,f103,f131,f147,f198])).

% (17262)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% (17265)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f198,plain,
    ( spl3_1
    | spl3_2
    | ~ spl3_8
    | spl3_16
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl3_1
    | spl3_2
    | ~ spl3_8
    | spl3_16
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f160,f191])).

fof(f191,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl3_1
    | spl3_2
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f56,f61,f146])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k2_tarski(X0,X2),X1)
        | r2_hidden(X2,X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(k2_tarski(X0,X2),X1)
        | r2_hidden(X2,X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f61,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f56,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f160,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_8
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f130,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f130,plain,
    ( ~ r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_16
  <=> r1_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

% (17254)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f147,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f47,f145])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f131,plain,
    ( ~ spl3_16
    | spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f118,f101,f64,f128])).

fof(f64,plain,
    ( spl3_3
  <=> sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f101,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f118,plain,
    ( ~ r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_3
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f66,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f66,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f103,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f52,f101])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f43,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f87,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f42,f85])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f67,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f62,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:59:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (17258)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (17257)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (17267)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (17252)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (17266)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (17257)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f57,f62,f67,f87,f103,f131,f147,f198])).
% 0.21/0.48  % (17262)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (17265)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    spl3_1 | spl3_2 | ~spl3_8 | spl3_16 | ~spl3_20),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f197])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    $false | (spl3_1 | spl3_2 | ~spl3_8 | spl3_16 | ~spl3_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f160,f191])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | (spl3_1 | spl3_2 | ~spl3_20)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f56,f61,f146])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) ) | ~spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f145])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    spl3_20 <=> ! [X1,X0,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK2) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl3_2 <=> r2_hidden(sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~r2_hidden(sK0,sK2) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl3_1 <=> r2_hidden(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2) | (~spl3_8 | spl3_16)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f130,f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl3_8 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    ~r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    spl3_16 <=> r1_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  % (17254)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl3_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f145])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~spl3_16 | spl3_3 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f118,f101,f64,f128])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl3_3 <=> sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl3_12 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | (spl3_3 | ~spl3_12)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f66,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f52,f101])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f43,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f85])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f64])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.48    inference(negated_conjecture,[],[f21])).
% 0.21/0.48  fof(f21,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f59])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ~spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f54])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ~r2_hidden(sK0,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17257)------------------------------
% 0.21/0.48  % (17257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17257)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17259)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (17257)Memory used [KB]: 6140
% 0.21/0.48  % (17257)Time elapsed: 0.053 s
% 0.21/0.48  % (17257)------------------------------
% 0.21/0.48  % (17257)------------------------------
% 0.21/0.48  % (17251)Success in time 0.118 s
%------------------------------------------------------------------------------
