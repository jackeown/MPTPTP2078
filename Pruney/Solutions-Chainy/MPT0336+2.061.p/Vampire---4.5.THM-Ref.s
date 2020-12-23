%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:31 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   55 (  90 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  100 ( 197 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f405,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f368,f404])).

fof(f404,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f392,f232])).

fof(f232,plain,(
    ! [X3] : r1_xboole_0(k3_xboole_0(X3,sK1),sK2) ),
    inference(superposition,[],[f95,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f95,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(sK1,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f48,plain,(
    ! [X0] : r1_xboole_0(sK2,k3_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f26,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f26,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f392,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl4_1 ),
    inference(superposition,[],[f45,f78])).

fof(f78,plain,
    ( k3_xboole_0(sK0,sK1) = k2_tarski(sK3,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_1
  <=> k3_xboole_0(sK0,sK1) = k2_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f45,plain,(
    ! [X0] : ~ r1_xboole_0(k2_tarski(sK3,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f25,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f368,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f366,f147])).

fof(f147,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f140,f29])).

fof(f140,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f82,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f82,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_2
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f366,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f363,f55])).

fof(f55,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f49,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f26,f29])).

fof(f363,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f127,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f127,plain,(
    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f64,f37])).

fof(f64,plain,(
    ~ r1_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f29])).

fof(f27,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f72,f80,f76])).

fof(f72,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | k3_xboole_0(sK0,sK1) = k2_tarski(sK3,sK3) ),
    inference(resolution,[],[f39,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f31,f34,f34])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f39,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3)) ),
    inference(definition_unfolding,[],[f24,f34])).

fof(f24,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:45:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (25520)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.50  % (25501)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (25509)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (25512)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (25499)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (25503)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (25504)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (25508)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (25502)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (25528)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (25523)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (25522)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (25519)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (25516)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (25511)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (25500)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (25510)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (25505)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (25525)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.54  % (25506)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.55  % (25508)Refutation found. Thanks to Tanya!
% 1.40/0.55  % SZS status Theorem for theBenchmark
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f405,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(avatar_sat_refutation,[],[f83,f368,f404])).
% 1.40/0.55  fof(f404,plain,(
% 1.40/0.55    ~spl4_1),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f403])).
% 1.40/0.55  fof(f403,plain,(
% 1.40/0.55    $false | ~spl4_1),
% 1.40/0.55    inference(subsumption_resolution,[],[f392,f232])).
% 1.40/0.55  fof(f232,plain,(
% 1.40/0.55    ( ! [X3] : (r1_xboole_0(k3_xboole_0(X3,sK1),sK2)) )),
% 1.40/0.55    inference(superposition,[],[f95,f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.40/0.55  fof(f95,plain,(
% 1.40/0.55    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK1,X0),sK2)) )),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f48,f29])).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f21])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f3])).
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    ( ! [X0] : (r1_xboole_0(sK2,k3_xboole_0(sK1,X0))) )),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f26,f35])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f23])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.40/0.55    inference(ennf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    r1_xboole_0(sK2,sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f19])).
% 1.40/0.55  fof(f19,plain,(
% 1.40/0.55    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.40/0.55    inference(flattening,[],[f18])).
% 1.40/0.55  fof(f18,plain,(
% 1.40/0.55    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.40/0.55    inference(ennf_transformation,[],[f17])).
% 1.40/0.55  fof(f17,negated_conjecture,(
% 1.40/0.55    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.40/0.55    inference(negated_conjecture,[],[f16])).
% 1.40/0.55  fof(f16,conjecture,(
% 1.40/0.55    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.40/0.55  fof(f392,plain,(
% 1.40/0.55    ~r1_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl4_1),
% 1.40/0.55    inference(superposition,[],[f45,f78])).
% 1.40/0.55  fof(f78,plain,(
% 1.40/0.55    k3_xboole_0(sK0,sK1) = k2_tarski(sK3,sK3) | ~spl4_1),
% 1.40/0.55    inference(avatar_component_clause,[],[f76])).
% 1.40/0.55  fof(f76,plain,(
% 1.40/0.55    spl4_1 <=> k3_xboole_0(sK0,sK1) = k2_tarski(sK3,sK3)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.40/0.55  fof(f45,plain,(
% 1.40/0.55    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK3,X0),sK2)) )),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f25,f30])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f22])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.40/0.55    inference(ennf_transformation,[],[f15])).
% 1.40/0.55  fof(f15,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    r2_hidden(sK3,sK2)),
% 1.40/0.55    inference(cnf_transformation,[],[f19])).
% 1.40/0.55  fof(f368,plain,(
% 1.40/0.55    ~spl4_2),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f367])).
% 1.40/0.55  fof(f367,plain,(
% 1.40/0.55    $false | ~spl4_2),
% 1.40/0.55    inference(subsumption_resolution,[],[f366,f147])).
% 1.40/0.55  fof(f147,plain,(
% 1.40/0.55    r1_xboole_0(sK1,sK0) | ~spl4_2),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f140,f29])).
% 1.40/0.55  fof(f140,plain,(
% 1.40/0.55    r1_xboole_0(sK0,sK1) | ~spl4_2),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f82,f37])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f2])).
% 1.40/0.55  fof(f2,axiom,(
% 1.40/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.40/0.55  fof(f82,plain,(
% 1.40/0.55    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl4_2),
% 1.40/0.55    inference(avatar_component_clause,[],[f80])).
% 1.40/0.55  fof(f80,plain,(
% 1.40/0.55    spl4_2 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.40/0.55  fof(f366,plain,(
% 1.40/0.55    ~r1_xboole_0(sK1,sK0)),
% 1.40/0.55    inference(subsumption_resolution,[],[f363,f55])).
% 1.40/0.55  fof(f55,plain,(
% 1.40/0.55    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f49,f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f2])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    r1_xboole_0(sK1,sK2)),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f26,f29])).
% 1.40/0.55  fof(f363,plain,(
% 1.40/0.55    k1_xboole_0 != k3_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0)),
% 1.40/0.55    inference(superposition,[],[f127,f28])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f20])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f5])).
% 1.40/0.55  fof(f5,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 1.40/0.55  fof(f127,plain,(
% 1.40/0.55    k1_xboole_0 != k3_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f64,f37])).
% 1.40/0.55  fof(f64,plain,(
% 1.40/0.55    ~r1_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f27,f29])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f19])).
% 1.40/0.55  fof(f83,plain,(
% 1.40/0.55    spl4_1 | spl4_2),
% 1.40/0.55    inference(avatar_split_clause,[],[f72,f80,f76])).
% 1.40/0.55  fof(f72,plain,(
% 1.40/0.55    k1_xboole_0 = k3_xboole_0(sK0,sK1) | k3_xboole_0(sK0,sK1) = k2_tarski(sK3,sK3)),
% 1.40/0.55    inference(resolution,[],[f39,f42])).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0 | ~r1_tarski(X0,k2_tarski(X1,X1))) )),
% 1.40/0.55    inference(definition_unfolding,[],[f31,f34,f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f6])).
% 1.40/0.55  fof(f6,axiom,(
% 1.40/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,axiom,(
% 1.40/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    r1_tarski(k3_xboole_0(sK0,sK1),k2_tarski(sK3,sK3))),
% 1.40/0.55    inference(definition_unfolding,[],[f24,f34])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.40/0.55    inference(cnf_transformation,[],[f19])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (25508)------------------------------
% 1.40/0.55  % (25508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (25508)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (25508)Memory used [KB]: 10874
% 1.40/0.55  % (25508)Time elapsed: 0.129 s
% 1.40/0.55  % (25508)------------------------------
% 1.40/0.55  % (25508)------------------------------
% 1.40/0.55  % (25498)Success in time 0.185 s
%------------------------------------------------------------------------------
