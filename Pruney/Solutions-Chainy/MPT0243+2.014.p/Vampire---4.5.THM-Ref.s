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
% DateTime   : Thu Dec  3 12:37:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 121 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  204 ( 367 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f66,f67,f125,f141,f147])).

fof(f147,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f144,f60])).

fof(f60,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f144,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f128,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f128,plain,
    ( r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f55,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f55,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_1
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f141,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(resolution,[],[f132,f55])).

fof(f132,plain,
    ( ! [X1] : ~ r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(sK1)),sK2)
    | spl3_3 ),
    inference(resolution,[],[f126,f50])).

fof(f50,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))
      | k1_tarski(X2) != X0 ) ),
    inference(definition_unfolding,[],[f39,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f126,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tarski(sK1),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl3_3 ),
    inference(resolution,[],[f64,f73])).

fof(f73,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(X7,X6)
      | ~ r1_tarski(k1_tarski(X7),X5)
      | ~ r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f34,f29])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f64,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f125,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f121,f56])).

fof(f56,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f121,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f116,f98])).

fof(f98,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | r1_tarski(k2_xboole_0(X1,k1_tarski(sK1)),sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f80,f63])).

fof(f63,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k2_xboole_0(X0,k1_tarski(X1)),X2) ) ),
    inference(resolution,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f116,plain,
    ( r1_tarski(k1_tarski(sK0),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f112,f33])).

fof(f112,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f109,f59])).

fof(f59,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f109,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | r1_tarski(k2_xboole_0(k1_tarski(X2),k1_tarski(sK0)),sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f97,f30])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(k2_xboole_0(X0,k1_tarski(sK0)),sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f80,f59])).

fof(f67,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f43,f58,f54])).

fof(f43,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f25,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f66,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f42,f62,f54])).

fof(f42,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f26,f28])).

fof(f26,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f62,f58,f54])).

fof(f41,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (9486)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (9478)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (9503)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (9496)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (9494)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (9485)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (9478)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (9488)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (9476)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (9475)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f65,f66,f67,f125,f141,f147])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ~spl3_1 | spl3_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f146])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    $false | (~spl3_1 | spl3_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f144,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ~r2_hidden(sK0,sK2) | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    spl3_2 <=> r2_hidden(sK0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | ~spl3_1),
% 0.21/0.52    inference(resolution,[],[f128,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    r1_tarski(k1_tarski(sK0),sK2) | ~spl3_1),
% 0.21/0.52    inference(resolution,[],[f55,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl3_1 <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~spl3_1 | spl3_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    $false | (~spl3_1 | spl3_3)),
% 0.21/0.52    inference(resolution,[],[f132,f55])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(k2_xboole_0(k1_tarski(X1),k1_tarski(sK1)),sK2)) ) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f126,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) | k1_tarski(X2) != X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f39,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.21/0.52    inference(nnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k1_tarski(sK1),X0) | ~r1_tarski(X0,sK2)) ) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f64,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (r2_hidden(X7,X6) | ~r1_tarski(k1_tarski(X7),X5) | ~r1_tarski(X5,X6)) )),
% 0.21/0.52    inference(resolution,[],[f34,f29])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK2) | spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    spl3_3 <=> r2_hidden(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    $false | (spl3_1 | ~spl3_2 | ~spl3_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f121,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ~r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f54])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | (~spl3_2 | ~spl3_3)),
% 0.21/0.52    inference(resolution,[],[f116,f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(X1,sK2) | r1_tarski(k2_xboole_0(X1,k1_tarski(sK1)),sK2)) ) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f80,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    r2_hidden(sK1,sK2) | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f62])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | ~r1_tarski(X0,X2) | r1_tarski(k2_xboole_0(X0,k1_tarski(X1)),X2)) )),
% 0.21/0.52    inference(resolution,[],[f35,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    r1_tarski(k1_tarski(sK0),sK2) | ~spl3_2),
% 0.21/0.52    inference(resolution,[],[f112,f33])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)),sK2) | ~spl3_2),
% 0.21/0.52    inference(resolution,[],[f109,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f58])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK2) | r1_tarski(k2_xboole_0(k1_tarski(X2),k1_tarski(sK0)),sK2)) ) | ~spl3_2),
% 0.21/0.52    inference(resolution,[],[f97,f30])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(k2_xboole_0(X0,k1_tarski(sK0)),sK2)) ) | ~spl3_2),
% 0.21/0.52    inference(resolution,[],[f80,f59])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl3_1 | spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f58,f54])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f28])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    r2_hidden(sK0,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f8])).
% 0.21/0.52  fof(f8,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    spl3_1 | spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f62,f54])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    r2_hidden(sK1,sK2) | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.21/0.52    inference(definition_unfolding,[],[f26,f28])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    r2_hidden(sK1,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f62,f58,f54])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 0.21/0.52    inference(definition_unfolding,[],[f27,f28])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (9478)------------------------------
% 0.21/0.52  % (9478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9478)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (9478)Memory used [KB]: 10746
% 0.21/0.52  % (9478)Time elapsed: 0.104 s
% 0.21/0.52  % (9478)------------------------------
% 0.21/0.52  % (9478)------------------------------
% 0.21/0.53  % (9474)Success in time 0.17 s
%------------------------------------------------------------------------------
