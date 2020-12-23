%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 172 expanded)
%              Number of leaves         :   12 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  174 ( 549 expanded)
%              Number of equality atoms :   57 ( 200 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f112,f137,f147,f167])).

fof(f167,plain,
    ( ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f165,f28])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK0 != sK1
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK0 != sK1
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f165,plain,
    ( sK0 = sK1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f93,f164])).

fof(f164,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f160,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f160,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f111,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f111,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(X2,sK1),sK0)
        | k3_xboole_0(X2,sK1) = X2 )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_5
  <=> ! [X2] :
        ( k3_xboole_0(X2,sK1) = X2
        | ~ r2_hidden(sK3(X2,sK1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f93,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f92,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f92,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f88,f31])).

fof(f88,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f86,f35])).

fof(f86,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK3(X4,sK0),sK1)
        | k3_xboole_0(X4,sK0) = X4 )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_2
  <=> ! [X4] :
        ( k3_xboole_0(X4,sK0) = X4
        | ~ r2_hidden(sK3(X4,sK0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f147,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f143,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f143,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(superposition,[],[f41,f124])).

fof(f124,plain,
    ( ! [X0] : sK1 = k3_xboole_0(sK1,X0)
    | ~ spl4_4 ),
    inference(resolution,[],[f122,f31])).

fof(f122,plain,
    ( ! [X9] : r1_tarski(sK1,X9)
    | ~ spl4_4 ),
    inference(resolution,[],[f108,f35])).

fof(f108,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_4
  <=> ! [X3] : ~ r2_hidden(X3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

% (27168)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f41,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f40,f30])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f31,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f137,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f131,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f131,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(superposition,[],[f41,f123])).

fof(f123,plain,
    ( ! [X0] : sK0 = k3_xboole_0(sK0,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f117,f31])).

fof(f117,plain,
    ( ! [X9] : r1_tarski(sK0,X9)
    | ~ spl4_1 ),
    inference(resolution,[],[f83,f35])).

fof(f83,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl4_1
  <=> ! [X5] : ~ r2_hidden(X5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f112,plain,
    ( spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f98,f110,f107])).

fof(f98,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,sK1) = X2
      | ~ r2_hidden(X3,sK1)
      | ~ r2_hidden(sK3(X2,sK1),sK0) ) ),
    inference(resolution,[],[f79,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,sK1),X1),k2_zfmisc_1(sK0,sK1))
      | k3_xboole_0(X0,sK1) = X0 ) ),
    inference(superposition,[],[f56,f25])).

fof(f25,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),X2),k2_zfmisc_1(X1,X3))
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f53,f31])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),X2),k2_zfmisc_1(X1,X3)) ) ),
    inference(resolution,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f75,f85,f82])).

fof(f75,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X4,sK0) = X4
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(sK3(X4,sK0),sK1) ) ),
    inference(resolution,[],[f56,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f39,f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:23:34 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.52  % (27182)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (27170)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (27190)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (27178)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (27178)Refutation not found, incomplete strategy% (27178)------------------------------
% 0.21/0.54  % (27178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27178)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27178)Memory used [KB]: 10618
% 0.21/0.54  % (27178)Time elapsed: 0.117 s
% 0.21/0.54  % (27178)------------------------------
% 0.21/0.54  % (27178)------------------------------
% 0.21/0.54  % (27194)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (27194)Refutation not found, incomplete strategy% (27194)------------------------------
% 0.21/0.54  % (27194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27194)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27194)Memory used [KB]: 10618
% 0.21/0.54  % (27194)Time elapsed: 0.131 s
% 0.21/0.54  % (27194)------------------------------
% 0.21/0.54  % (27194)------------------------------
% 0.21/0.54  % (27176)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (27170)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f87,f112,f137,f147,f167])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    ~spl4_2 | ~spl4_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f166])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    $false | (~spl4_2 | ~spl4_5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f165,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    sK0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK0 != sK1 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.55    inference(flattening,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    inference(negated_conjecture,[],[f7])).
% 0.21/0.55  fof(f7,conjecture,(
% 0.21/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    sK0 = sK1 | (~spl4_2 | ~spl4_5)),
% 0.21/0.55    inference(backward_demodulation,[],[f93,f164])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    sK0 = k3_xboole_0(sK0,sK1) | ~spl4_5),
% 0.21/0.55    inference(subsumption_resolution,[],[f160,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    sK0 = k3_xboole_0(sK0,sK1) | r1_tarski(sK0,sK1) | ~spl4_5),
% 0.21/0.55    inference(resolution,[],[f111,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(sK3(X2,sK1),sK0) | k3_xboole_0(X2,sK1) = X2) ) | ~spl4_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f110])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    spl4_5 <=> ! [X2] : (k3_xboole_0(X2,sK1) = X2 | ~r2_hidden(sK3(X2,sK1),sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK0,sK1) | ~spl4_2),
% 0.21/0.55    inference(superposition,[],[f92,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK1,sK0) | ~spl4_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f88,f31])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    sK1 = k3_xboole_0(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl4_2),
% 0.21/0.55    inference(resolution,[],[f86,f35])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X4] : (~r2_hidden(sK3(X4,sK0),sK1) | k3_xboole_0(X4,sK0) = X4) ) | ~spl4_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f85])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    spl4_2 <=> ! [X4] : (k3_xboole_0(X4,sK0) = X4 | ~r2_hidden(sK3(X4,sK0),sK1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    ~spl4_4),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f146])).
% 0.21/0.55  fof(f146,plain,(
% 0.21/0.55    $false | ~spl4_4),
% 0.21/0.55    inference(subsumption_resolution,[],[f143,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    k1_xboole_0 != sK1),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    k1_xboole_0 = sK1 | ~spl4_4),
% 0.21/0.55    inference(superposition,[],[f41,f124])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    ( ! [X0] : (sK1 = k3_xboole_0(sK1,X0)) ) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f122,f31])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    ( ! [X9] : (r1_tarski(sK1,X9)) ) | ~spl4_4),
% 0.21/0.55    inference(resolution,[],[f108,f35])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ( ! [X3] : (~r2_hidden(X3,sK1)) ) | ~spl4_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    spl4_4 <=> ! [X3] : ~r2_hidden(X3,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.55  % (27168)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f40,f30])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f31,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    ~spl4_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    $false | ~spl4_1),
% 0.21/0.55    inference(subsumption_resolution,[],[f131,f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    k1_xboole_0 = sK0 | ~spl4_1),
% 0.21/0.55    inference(superposition,[],[f41,f123])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    ( ! [X0] : (sK0 = k3_xboole_0(sK0,X0)) ) | ~spl4_1),
% 0.21/0.55    inference(resolution,[],[f117,f31])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    ( ! [X9] : (r1_tarski(sK0,X9)) ) | ~spl4_1),
% 0.21/0.55    inference(resolution,[],[f83,f35])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X5] : (~r2_hidden(X5,sK0)) ) | ~spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    spl4_1 <=> ! [X5] : ~r2_hidden(X5,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    spl4_4 | spl4_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f98,f110,f107])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ( ! [X2,X3] : (k3_xboole_0(X2,sK1) = X2 | ~r2_hidden(X3,sK1) | ~r2_hidden(sK3(X2,sK1),sK0)) )),
% 0.21/0.55    inference(resolution,[],[f79,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.55    inference(nnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK3(X0,sK1),X1),k2_zfmisc_1(sK0,sK1)) | k3_xboole_0(X0,sK1) = X0) )),
% 0.21/0.55    inference(superposition,[],[f56,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),X2),k2_zfmisc_1(X1,X3)) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(resolution,[],[f53,f31])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1),X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.55    inference(resolution,[],[f37,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    spl4_1 | spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f75,f85,f82])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X4,X5] : (k3_xboole_0(X4,sK0) = X4 | ~r2_hidden(X5,sK0) | ~r2_hidden(sK3(X4,sK0),sK1)) )),
% 0.21/0.55    inference(resolution,[],[f56,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.55    inference(superposition,[],[f39,f25])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (27170)------------------------------
% 0.21/0.55  % (27170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27170)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (27170)Memory used [KB]: 10746
% 0.21/0.55  % (27170)Time elapsed: 0.126 s
% 0.21/0.55  % (27170)------------------------------
% 0.21/0.55  % (27170)------------------------------
% 0.21/0.55  % (27162)Success in time 0.191 s
%------------------------------------------------------------------------------
