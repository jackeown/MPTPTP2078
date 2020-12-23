%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:26 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   50 (  91 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 300 expanded)
%              Number of equality atoms :   27 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f121,f126,f136,f163,f175,f269,f272,f345])).

fof(f345,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f120,f125,f161,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f161,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl5_5
  <=> r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f125,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f120,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f272,plain,
    ( spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f162,f124,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f124,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f123])).

fof(f162,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f160])).

fof(f269,plain,
    ( spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f266])).

% (12072)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f266,plain,
    ( $false
    | spl5_2
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f119,f162,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f119,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f118])).

fof(f175,plain,
    ( ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f174,f114,f160])).

fof(f114,plain,
    ( spl5_1
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f174,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | spl5_1 ),
    inference(trivial_inequality_removal,[],[f171])).

fof(f171,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | spl5_1 ),
    inference(superposition,[],[f115,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f115,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f163,plain,
    ( spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f158,f114,f160])).

fof(f158,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f77,f116])).

fof(f116,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f136,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f135,f114,f123,f118])).

fof(f135,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl5_1 ),
    inference(trivial_inequality_removal,[],[f134])).

fof(f134,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f60,f116])).

fof(f60,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f126,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f59,f123,f114])).

fof(f59,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f121,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f58,f118,f114])).

% (12057)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f58,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:48:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (12044)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (12066)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  % (12056)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (12052)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (12048)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (12060)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.54  % (12045)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.38/0.54  % (12043)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.54  % (12047)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.38/0.54  % (12046)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.38/0.54  % (12066)Refutation found. Thanks to Tanya!
% 1.38/0.54  % SZS status Theorem for theBenchmark
% 1.38/0.54  % (12058)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.54  % SZS output start Proof for theBenchmark
% 1.38/0.54  fof(f346,plain,(
% 1.38/0.54    $false),
% 1.38/0.54    inference(avatar_sat_refutation,[],[f121,f126,f136,f163,f175,f269,f272,f345])).
% 1.38/0.54  fof(f345,plain,(
% 1.38/0.54    ~spl5_2 | ~spl5_3 | spl5_5),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f333])).
% 1.38/0.54  fof(f333,plain,(
% 1.38/0.54    $false | (~spl5_2 | ~spl5_3 | spl5_5)),
% 1.38/0.54    inference(unit_resulting_resolution,[],[f120,f125,f161,f63])).
% 1.38/0.54  fof(f63,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f48])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.38/0.54    inference(flattening,[],[f47])).
% 1.38/0.54  fof(f47,plain,(
% 1.38/0.54    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.38/0.54    inference(nnf_transformation,[],[f21])).
% 1.38/0.54  fof(f21,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.38/0.54  fof(f161,plain,(
% 1.38/0.54    ~r1_tarski(k2_tarski(sK0,sK1),sK2) | spl5_5),
% 1.38/0.54    inference(avatar_component_clause,[],[f160])).
% 1.38/0.54  fof(f160,plain,(
% 1.38/0.54    spl5_5 <=> r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.38/0.54  fof(f125,plain,(
% 1.38/0.54    r2_hidden(sK1,sK2) | ~spl5_3),
% 1.38/0.54    inference(avatar_component_clause,[],[f123])).
% 1.38/0.54  fof(f123,plain,(
% 1.38/0.54    spl5_3 <=> r2_hidden(sK1,sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.38/0.54  fof(f120,plain,(
% 1.38/0.54    r2_hidden(sK0,sK2) | ~spl5_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f118])).
% 1.38/0.54  fof(f118,plain,(
% 1.38/0.54    spl5_2 <=> r2_hidden(sK0,sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.38/0.54  fof(f272,plain,(
% 1.38/0.54    spl5_3 | ~spl5_5),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f271])).
% 1.38/0.54  fof(f271,plain,(
% 1.38/0.54    $false | (spl5_3 | ~spl5_5)),
% 1.38/0.54    inference(unit_resulting_resolution,[],[f162,f124,f62])).
% 1.38/0.54  fof(f62,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f48])).
% 1.38/0.54  fof(f124,plain,(
% 1.38/0.54    ~r2_hidden(sK1,sK2) | spl5_3),
% 1.38/0.54    inference(avatar_component_clause,[],[f123])).
% 1.38/0.54  fof(f162,plain,(
% 1.38/0.54    r1_tarski(k2_tarski(sK0,sK1),sK2) | ~spl5_5),
% 1.38/0.54    inference(avatar_component_clause,[],[f160])).
% 1.38/0.54  fof(f269,plain,(
% 1.38/0.54    spl5_2 | ~spl5_5),
% 1.38/0.54    inference(avatar_contradiction_clause,[],[f266])).
% 1.38/0.54  % (12072)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.38/0.54  fof(f266,plain,(
% 1.38/0.54    $false | (spl5_2 | ~spl5_5)),
% 1.38/0.54    inference(unit_resulting_resolution,[],[f119,f162,f61])).
% 1.38/0.54  fof(f61,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f48])).
% 1.38/0.54  fof(f119,plain,(
% 1.38/0.54    ~r2_hidden(sK0,sK2) | spl5_2),
% 1.38/0.54    inference(avatar_component_clause,[],[f118])).
% 1.38/0.54  fof(f175,plain,(
% 1.38/0.54    ~spl5_5 | spl5_1),
% 1.38/0.54    inference(avatar_split_clause,[],[f174,f114,f160])).
% 1.38/0.54  fof(f114,plain,(
% 1.38/0.54    spl5_1 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.38/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.38/0.54  fof(f174,plain,(
% 1.38/0.54    ~r1_tarski(k2_tarski(sK0,sK1),sK2) | spl5_1),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f171])).
% 1.38/0.54  fof(f171,plain,(
% 1.38/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_tarski(sK0,sK1),sK2) | spl5_1),
% 1.38/0.54    inference(superposition,[],[f115,f78])).
% 1.38/0.54  fof(f78,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f55])).
% 1.38/0.54  fof(f55,plain,(
% 1.38/0.54    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.38/0.54    inference(nnf_transformation,[],[f8])).
% 1.38/0.54  fof(f8,axiom,(
% 1.38/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.38/0.54  fof(f115,plain,(
% 1.38/0.54    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | spl5_1),
% 1.38/0.54    inference(avatar_component_clause,[],[f114])).
% 1.38/0.54  fof(f163,plain,(
% 1.38/0.54    spl5_5 | ~spl5_1),
% 1.38/0.54    inference(avatar_split_clause,[],[f158,f114,f160])).
% 1.38/0.54  fof(f158,plain,(
% 1.38/0.54    r1_tarski(k2_tarski(sK0,sK1),sK2) | ~spl5_1),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f153])).
% 1.38/0.54  fof(f153,plain,(
% 1.38/0.54    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_tarski(sK0,sK1),sK2) | ~spl5_1),
% 1.38/0.54    inference(superposition,[],[f77,f116])).
% 1.38/0.54  fof(f116,plain,(
% 1.38/0.54    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl5_1),
% 1.38/0.54    inference(avatar_component_clause,[],[f114])).
% 1.38/0.54  fof(f77,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f55])).
% 1.38/0.54  fof(f136,plain,(
% 1.38/0.54    ~spl5_2 | ~spl5_3 | ~spl5_1),
% 1.38/0.54    inference(avatar_split_clause,[],[f135,f114,f123,f118])).
% 1.38/0.54  fof(f135,plain,(
% 1.38/0.54    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~spl5_1),
% 1.38/0.54    inference(trivial_inequality_removal,[],[f134])).
% 1.38/0.54  fof(f134,plain,(
% 1.38/0.54    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~spl5_1),
% 1.38/0.54    inference(forward_demodulation,[],[f60,f116])).
% 1.38/0.54  fof(f60,plain,(
% 1.38/0.54    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.38/0.54    inference(cnf_transformation,[],[f46])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f45])).
% 1.38/0.55  fof(f45,plain,(
% 1.38/0.55    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f44,plain,(
% 1.38/0.55    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.38/0.55    inference(flattening,[],[f43])).
% 1.38/0.55  fof(f43,plain,(
% 1.38/0.55    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.38/0.55    inference(nnf_transformation,[],[f30])).
% 1.38/0.55  fof(f30,plain,(
% 1.38/0.55    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.38/0.55    inference(ennf_transformation,[],[f26])).
% 1.38/0.55  fof(f26,negated_conjecture,(
% 1.38/0.55    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.38/0.55    inference(negated_conjecture,[],[f25])).
% 1.38/0.55  fof(f25,conjecture,(
% 1.38/0.55    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.38/0.55  fof(f126,plain,(
% 1.38/0.55    spl5_1 | spl5_3),
% 1.38/0.55    inference(avatar_split_clause,[],[f59,f123,f114])).
% 1.38/0.55  fof(f59,plain,(
% 1.38/0.55    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.38/0.55    inference(cnf_transformation,[],[f46])).
% 1.38/0.55  fof(f121,plain,(
% 1.38/0.55    spl5_1 | spl5_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f58,f118,f114])).
% 1.38/0.55  % (12057)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.38/0.55  fof(f58,plain,(
% 1.38/0.55    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.38/0.55    inference(cnf_transformation,[],[f46])).
% 1.38/0.55  % SZS output end Proof for theBenchmark
% 1.38/0.55  % (12066)------------------------------
% 1.38/0.55  % (12066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (12066)Termination reason: Refutation
% 1.38/0.55  
% 1.38/0.55  % (12066)Memory used [KB]: 11001
% 1.38/0.55  % (12066)Time elapsed: 0.078 s
% 1.38/0.55  % (12066)------------------------------
% 1.38/0.55  % (12066)------------------------------
% 1.38/0.55  % (12049)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.55  % (12070)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.55  % (12071)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.55  % (12064)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.55  % (12040)Success in time 0.188 s
%------------------------------------------------------------------------------
