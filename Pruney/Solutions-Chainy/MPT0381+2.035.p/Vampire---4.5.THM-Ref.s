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
% DateTime   : Thu Dec  3 12:45:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   15 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :  147 ( 207 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f63,f90,f99,f109,f154,f159])).

fof(f159,plain,
    ( ~ spl2_3
    | spl2_12
    | ~ spl2_22 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl2_3
    | spl2_12
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f54,f155])).

fof(f155,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl2_12
    | ~ spl2_22 ),
    inference(superposition,[],[f98,f153])).

fof(f153,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl2_22
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f98,plain,
    ( ~ v1_xboole_0(sK1)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl2_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f54,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f154,plain,
    ( spl2_22
    | ~ spl2_1
    | spl2_2
    | ~ spl2_11
    | spl2_12
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f119,f107,f96,f88,f47,f42,f151])).

fof(f42,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f47,plain,
    ( spl2_2
  <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f88,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X1,X0)
        | ~ r2_hidden(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f107,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f119,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_1
    | spl2_2
    | ~ spl2_11
    | spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f114,f117])).

fof(f117,plain,
    ( m1_subset_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_11
    | spl2_12 ),
    inference(unit_resulting_resolution,[],[f44,f98,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f44,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK0,sK1)
    | spl2_2
    | ~ spl2_14 ),
    inference(resolution,[],[f108,f49])).

fof(f49,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,X0) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f107])).

fof(f109,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f33,f107])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f99,plain,
    ( ~ spl2_12
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f69,f61,f42,f96])).

fof(f61,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f69,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f44,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f90,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f30,f88])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f63,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f55,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f40,f52])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f25,f26])).

fof(f26,plain,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_subset_1(X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f25,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

fof(f50,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f24,f47])).

fof(f24,plain,(
    ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
        & r2_hidden(X0,X1) )
   => ( ~ m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f45,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f42])).

fof(f23,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (16309)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (16309)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (16313)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (16305)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (16314)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (16320)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (16316)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (16307)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (16318)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (16317)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f45,f50,f55,f63,f90,f99,f109,f154,f159])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    ~spl2_3 | spl2_12 | ~spl2_22),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    $false | (~spl2_3 | spl2_12 | ~spl2_22)),
% 0.21/0.47    inference(subsumption_resolution,[],[f54,f155])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ~v1_xboole_0(k1_xboole_0) | (spl2_12 | ~spl2_22)),
% 0.21/0.47    inference(superposition,[],[f98,f153])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~spl2_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f151])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    spl2_22 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ~v1_xboole_0(sK1) | spl2_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl2_12 <=> v1_xboole_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl2_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    spl2_22 | ~spl2_1 | spl2_2 | ~spl2_11 | spl2_12 | ~spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f119,f107,f96,f88,f47,f42,f151])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl2_2 <=> m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl2_11 <=> ! [X1,X0] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    spl2_14 <=> ! [X1,X0] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | (~spl2_1 | spl2_2 | ~spl2_11 | spl2_12 | ~spl2_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f114,f117])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    m1_subset_1(sK0,sK1) | (~spl2_1 | ~spl2_11 | spl2_12)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f44,f98,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f42])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~m1_subset_1(sK0,sK1) | (spl2_2 | ~spl2_14)),
% 0.21/0.47    inference(resolution,[],[f108,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) | spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) ) | ~spl2_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f107])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f107])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ~spl2_12 | ~spl2_1 | ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f69,f61,f42,f96])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl2_5 <=> ! [X1,X0] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ~v1_xboole_0(sK1) | (~spl2_1 | ~spl2_5)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f44,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) ) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f61])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl2_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f88])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f61])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f52])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(forward_demodulation,[],[f25,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (k1_subset_1(X0) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : k1_subset_1(X0) = k1_xboole_0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0] : (v1_xboole_0(k1_subset_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : v1_xboole_0(k1_subset_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f47])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1)) => (~m1_subset_1(k1_tarski(sK0),k1_zfmisc_1(sK1)) & r2_hidden(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) & r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f13])).
% 0.21/0.47  fof(f13,conjecture,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f42])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16309)------------------------------
% 0.21/0.47  % (16309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16309)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16309)Memory used [KB]: 6140
% 0.21/0.47  % (16309)Time elapsed: 0.054 s
% 0.21/0.47  % (16309)------------------------------
% 0.21/0.47  % (16309)------------------------------
% 0.21/0.47  % (16310)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (16303)Success in time 0.117 s
%------------------------------------------------------------------------------
