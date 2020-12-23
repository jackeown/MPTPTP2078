%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:41 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   42 (  99 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 258 expanded)
%              Number of equality atoms :   22 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f37,f123,f387])).

fof(f387,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f363,f333])).

fof(f333,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_tarski(sK1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f330])).

fof(f330,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_tarski(sK1))
        | ~ r2_hidden(X4,k1_tarski(sK1)) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f26,f166])).

fof(f166,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f157,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f157,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f35,f148])).

fof(f148,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X4,k1_tarski(sK1)) )
    | ~ spl3_1 ),
    inference(superposition,[],[f26,f30])).

fof(f30,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl3_1
  <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f363,plain,
    ( r2_hidden(sK2(k1_tarski(sK1),sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f124,f333,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f124,plain,
    ( k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f123,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f121,f31])).

fof(f31,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f121,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f120,f103])).

fof(f103,plain,
    ( ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f100,f66])).

fof(f66,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X4,k1_tarski(sK1)) )
    | spl3_2 ),
    inference(superposition,[],[f26,f38])).

fof(f38,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0)
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f34,f23])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f100,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl3_1 ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,
    ( ! [X1] :
        ( sK0 != X1
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X1),sK0)
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X1),X1) )
    | spl3_1 ),
    inference(superposition,[],[f31,f18])).

fof(f120,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f107,f100])).

fof(f107,plain,
    ( ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | spl3_1 ),
    inference(resolution,[],[f100,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f15,f33,f29])).

fof(f15,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f36,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f16,f33,f29])).

fof(f16,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:27:30 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.53  % (19274)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (19283)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (19291)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (19299)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (19277)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (19286)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.57  % (19271)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.58  % (19288)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.58  % (19276)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (19293)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (19285)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.82/0.59  % (19280)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.82/0.59  % (19272)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.82/0.60  % (19292)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.82/0.60  % (19288)Refutation not found, incomplete strategy% (19288)------------------------------
% 1.82/0.60  % (19288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.60  % (19288)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.60  
% 1.82/0.60  % (19288)Memory used [KB]: 10618
% 1.82/0.60  % (19288)Time elapsed: 0.158 s
% 1.82/0.60  % (19288)------------------------------
% 1.82/0.60  % (19288)------------------------------
% 1.82/0.60  % (19300)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.82/0.60  % (19297)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.82/0.60  % (19281)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.82/0.61  % (19280)Refutation found. Thanks to Tanya!
% 1.82/0.61  % SZS status Theorem for theBenchmark
% 1.82/0.61  % (19289)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.82/0.61  % SZS output start Proof for theBenchmark
% 1.82/0.61  fof(f389,plain,(
% 1.82/0.61    $false),
% 1.82/0.61    inference(avatar_sat_refutation,[],[f36,f37,f123,f387])).
% 1.82/0.61  fof(f387,plain,(
% 1.82/0.61    ~spl3_1 | ~spl3_2),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f386])).
% 1.82/0.61  fof(f386,plain,(
% 1.82/0.61    $false | (~spl3_1 | ~spl3_2)),
% 1.82/0.61    inference(subsumption_resolution,[],[f363,f333])).
% 1.82/0.61  fof(f333,plain,(
% 1.82/0.61    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK1))) ) | (~spl3_1 | ~spl3_2)),
% 1.82/0.61    inference(duplicate_literal_removal,[],[f330])).
% 1.82/0.61  fof(f330,plain,(
% 1.82/0.61    ( ! [X4] : (~r2_hidden(X4,k1_tarski(sK1)) | ~r2_hidden(X4,k1_tarski(sK1))) ) | (~spl3_1 | ~spl3_2)),
% 1.82/0.61    inference(superposition,[],[f26,f166])).
% 1.82/0.61  fof(f166,plain,(
% 1.82/0.61    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | (~spl3_1 | ~spl3_2)),
% 1.82/0.61    inference(unit_resulting_resolution,[],[f157,f23])).
% 1.82/0.61  fof(f23,plain,(
% 1.82/0.61    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f11])).
% 1.82/0.61  fof(f11,axiom,(
% 1.82/0.61    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.82/0.61  fof(f157,plain,(
% 1.82/0.61    ~r2_hidden(sK1,k1_tarski(sK1)) | (~spl3_1 | ~spl3_2)),
% 1.82/0.61    inference(unit_resulting_resolution,[],[f35,f148])).
% 1.82/0.61  fof(f148,plain,(
% 1.82/0.61    ( ! [X4] : (~r2_hidden(X4,sK0) | ~r2_hidden(X4,k1_tarski(sK1))) ) | ~spl3_1),
% 1.82/0.61    inference(superposition,[],[f26,f30])).
% 1.82/0.61  fof(f30,plain,(
% 1.82/0.61    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl3_1),
% 1.82/0.61    inference(avatar_component_clause,[],[f29])).
% 1.82/0.61  fof(f29,plain,(
% 1.82/0.61    spl3_1 <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.82/0.61  fof(f35,plain,(
% 1.82/0.61    r2_hidden(sK1,sK0) | ~spl3_2),
% 1.82/0.61    inference(avatar_component_clause,[],[f33])).
% 1.82/0.61  fof(f33,plain,(
% 1.82/0.61    spl3_2 <=> r2_hidden(sK1,sK0)),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.82/0.61  fof(f26,plain,(
% 1.82/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.82/0.61    inference(equality_resolution,[],[f21])).
% 1.82/0.61  fof(f21,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.82/0.61    inference(cnf_transformation,[],[f3])).
% 1.82/0.61  fof(f3,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.82/0.61  fof(f363,plain,(
% 1.82/0.61    r2_hidden(sK2(k1_tarski(sK1),sK0,k1_tarski(sK1)),k1_tarski(sK1)) | (~spl3_1 | ~spl3_2)),
% 1.82/0.61    inference(unit_resulting_resolution,[],[f124,f333,f18])).
% 1.82/0.61  fof(f18,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.82/0.61    inference(cnf_transformation,[],[f3])).
% 1.82/0.61  fof(f124,plain,(
% 1.82/0.61    k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK0) | ~spl3_2),
% 1.82/0.61    inference(unit_resulting_resolution,[],[f35,f24])).
% 1.82/0.61  fof(f24,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f11])).
% 1.82/0.61  fof(f123,plain,(
% 1.82/0.61    spl3_1 | spl3_2),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f122])).
% 1.82/0.61  fof(f122,plain,(
% 1.82/0.61    $false | (spl3_1 | spl3_2)),
% 1.82/0.61    inference(subsumption_resolution,[],[f121,f31])).
% 1.82/0.61  fof(f31,plain,(
% 1.82/0.61    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | spl3_1),
% 1.82/0.61    inference(avatar_component_clause,[],[f29])).
% 1.82/0.61  fof(f121,plain,(
% 1.82/0.61    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | (spl3_1 | spl3_2)),
% 1.82/0.61    inference(subsumption_resolution,[],[f120,f103])).
% 1.82/0.61  fof(f103,plain,(
% 1.82/0.61    ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | (spl3_1 | spl3_2)),
% 1.82/0.61    inference(unit_resulting_resolution,[],[f100,f66])).
% 1.82/0.61  fof(f66,plain,(
% 1.82/0.61    ( ! [X4] : (~r2_hidden(X4,sK0) | ~r2_hidden(X4,k1_tarski(sK1))) ) | spl3_2),
% 1.82/0.61    inference(superposition,[],[f26,f38])).
% 1.82/0.61  fof(f38,plain,(
% 1.82/0.61    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0) | spl3_2),
% 1.82/0.61    inference(unit_resulting_resolution,[],[f34,f23])).
% 1.82/0.61  fof(f34,plain,(
% 1.82/0.61    ~r2_hidden(sK1,sK0) | spl3_2),
% 1.82/0.61    inference(avatar_component_clause,[],[f33])).
% 1.82/0.61  fof(f100,plain,(
% 1.82/0.61    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl3_1),
% 1.82/0.61    inference(duplicate_literal_removal,[],[f99])).
% 1.82/0.61  fof(f99,plain,(
% 1.82/0.61    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl3_1),
% 1.82/0.61    inference(equality_resolution,[],[f44])).
% 1.82/0.61  fof(f44,plain,(
% 1.82/0.61    ( ! [X1] : (sK0 != X1 | r2_hidden(sK2(sK0,k1_tarski(sK1),X1),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),X1),X1)) ) | spl3_1),
% 1.82/0.61    inference(superposition,[],[f31,f18])).
% 1.82/0.61  fof(f120,plain,(
% 1.82/0.61    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | spl3_1),
% 1.82/0.61    inference(subsumption_resolution,[],[f107,f100])).
% 1.82/0.61  fof(f107,plain,(
% 1.82/0.61    ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | spl3_1),
% 1.82/0.61    inference(resolution,[],[f100,f17])).
% 1.82/0.61  fof(f17,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.82/0.61    inference(cnf_transformation,[],[f3])).
% 1.82/0.61  fof(f37,plain,(
% 1.82/0.61    spl3_1 | ~spl3_2),
% 1.82/0.61    inference(avatar_split_clause,[],[f15,f33,f29])).
% 1.82/0.61  fof(f15,plain,(
% 1.82/0.61    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.82/0.61    inference(cnf_transformation,[],[f14])).
% 1.82/0.61  fof(f14,plain,(
% 1.82/0.61    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.82/0.61    inference(ennf_transformation,[],[f13])).
% 1.82/0.61  fof(f13,negated_conjecture,(
% 1.82/0.61    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.82/0.61    inference(negated_conjecture,[],[f12])).
% 1.82/0.61  fof(f12,conjecture,(
% 1.82/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.82/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.82/0.61  fof(f36,plain,(
% 1.82/0.61    ~spl3_1 | spl3_2),
% 1.82/0.61    inference(avatar_split_clause,[],[f16,f33,f29])).
% 1.82/0.62  fof(f16,plain,(
% 1.82/0.62    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.82/0.62    inference(cnf_transformation,[],[f14])).
% 1.82/0.62  % SZS output end Proof for theBenchmark
% 1.82/0.62  % (19280)------------------------------
% 1.82/0.62  % (19280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.62  % (19280)Termination reason: Refutation
% 1.82/0.62  
% 1.82/0.62  % (19280)Memory used [KB]: 10874
% 1.82/0.62  % (19280)Time elapsed: 0.179 s
% 1.82/0.62  % (19280)------------------------------
% 1.82/0.62  % (19280)------------------------------
% 2.05/0.62  % (19265)Success in time 0.262 s
%------------------------------------------------------------------------------
