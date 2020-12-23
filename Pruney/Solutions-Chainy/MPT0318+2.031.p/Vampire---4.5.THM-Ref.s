%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  88 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 163 expanded)
%              Number of equality atoms :   57 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f67,f81,f84,f88])).

fof(f88,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f12,f61,f49,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f49,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,
    ( k1_xboole_0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_3
  <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f84,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f12,f66])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f69,f73])).

fof(f73,plain,
    ( ! [X0] : ~ r2_hidden(sK1,X0)
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( ! [X0] :
        ( X0 != X0
        | ~ r2_hidden(sK1,X0) )
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f71,f13])).

fof(f13,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f71,plain,
    ( ! [X0] :
        ( k4_xboole_0(X0,k1_xboole_0) != X0
        | ~ r2_hidden(sK1,X0) )
    | ~ spl3_3 ),
    inference(superposition,[],[f31,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f20,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f14,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f15,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f69,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl3_3 ),
    inference(superposition,[],[f44,f62])).

fof(f44,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f67,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f58,f51,f64,f60])).

fof(f51,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f57])).

fof(f57,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f16,f53])).

fof(f53,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f54,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f30,f51,f47])).

fof(f30,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f11,f29,f29])).

fof(f11,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:47:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (1482)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (1508)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (1492)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (1489)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (1478)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (1508)Refutation not found, incomplete strategy% (1508)------------------------------
% 0.22/0.53  % (1508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1508)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (1492)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (1508)Memory used [KB]: 1663
% 0.22/0.53  % (1508)Time elapsed: 0.114 s
% 0.22/0.53  % (1508)------------------------------
% 0.22/0.53  % (1508)------------------------------
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f54,f67,f81,f84,f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ~spl3_1 | spl3_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    $false | (~spl3_1 | spl3_3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f12,f61,f49,f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl3_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    k1_xboole_0 != k2_enumset1(sK1,sK1,sK1,sK1) | spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl3_3 <=> k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    k1_xboole_0 != sK0),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ~spl3_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    $false | ~spl3_4),
% 0.22/0.53    inference(subsumption_resolution,[],[f12,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    spl3_4 <=> k1_xboole_0 = sK0),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ~spl3_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    $false | ~spl3_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f69,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK1,X0)) ) | ~spl3_3),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (X0 != X0 | ~r2_hidden(sK1,X0)) ) | ~spl3_3),
% 0.22/0.53    inference(forward_demodulation,[],[f71,f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) != X0 | ~r2_hidden(sK1,X0)) ) | ~spl3_3),
% 0.22/0.53    inference(superposition,[],[f31,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f20,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f14,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f15,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    r2_hidden(sK1,k1_xboole_0) | ~spl3_3),
% 0.22/0.53    inference(superposition,[],[f44,f62])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 0.22/0.53    inference(equality_resolution,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.53    inference(definition_unfolding,[],[f26,f28])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl3_3 | spl3_4 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f58,f51,f64,f60])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl3_2 <=> k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl3_2),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~spl3_2),
% 0.22/0.53    inference(superposition,[],[f16,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f51])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    spl3_1 | spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f30,f51,f47])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.22/0.53    inference(definition_unfolding,[],[f11,f29,f29])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (1492)------------------------------
% 0.22/0.53  % (1492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1492)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (1492)Memory used [KB]: 6140
% 0.22/0.53  % (1492)Time elapsed: 0.118 s
% 0.22/0.53  % (1492)------------------------------
% 0.22/0.53  % (1492)------------------------------
% 0.22/0.53  % (1477)Success in time 0.167 s
%------------------------------------------------------------------------------
