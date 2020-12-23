%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 123 expanded)
%              Number of leaves         :   11 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :  146 ( 350 expanded)
%              Number of equality atoms :   88 ( 264 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f32,f95,f124,f133,f135,f139,f140,f197])).

fof(f197,plain,
    ( spl2_10
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f196,f54,f89])).

fof(f89,plain,
    ( spl2_10
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f54,plain,
    ( spl2_6
  <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f196,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f183,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f183,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f182])).

fof(f182,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_6 ),
    inference(superposition,[],[f14,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f140,plain,
    ( ~ spl2_10
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f137,f38,f24,f89])).

fof(f24,plain,
    ( spl2_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f38,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f137,plain,
    ( k1_xboole_0 != sK0
    | spl2_1
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f26,f40])).

fof(f40,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f26,plain,
    ( sK0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f139,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f138,f38,f29,f54])).

fof(f29,plain,
    ( spl2_2
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f138,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f136,f21])).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f136,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f31,f40])).

fof(f31,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f135,plain,
    ( spl2_3
    | ~ spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f134,f29,f54,f38])).

fof(f134,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f129,f14])).

fof(f129,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f14,f31])).

fof(f133,plain,
    ( spl2_3
    | spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f132,f29,f48,f38])).

fof(f48,plain,
    ( spl2_5
  <=> sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f132,plain,
    ( sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f128,f14])).

fof(f128,plain,
    ( sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f18,f31])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f124,plain,
    ( spl2_6
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl2_6
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f108,f21])).

fof(f108,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl2_6
    | ~ spl2_10 ),
    inference(backward_demodulation,[],[f56,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f56,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f95,plain,
    ( spl2_10
    | spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f94,f48,f24,f89])).

fof(f94,plain,
    ( k1_xboole_0 = sK0
    | spl2_1
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f93,f14])).

fof(f93,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | spl2_1
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f85,f26])).

fof(f85,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK0)
    | ~ spl2_5 ),
    inference(superposition,[],[f18,f50])).

fof(f50,plain,
    ( sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f32,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f29])).

fof(f20,plain,(
    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(definition_unfolding,[],[f12,f19,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f12,plain,(
    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != sK1
    & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) )
   => ( sK0 != sK1
      & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_mcart_1)).

fof(f27,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:45:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (10666)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.50  % (10659)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.50  % (10651)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (10651)Refutation not found, incomplete strategy% (10651)------------------------------
% 0.22/0.50  % (10651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (10651)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (10651)Memory used [KB]: 10618
% 0.22/0.50  % (10651)Time elapsed: 0.090 s
% 0.22/0.50  % (10651)------------------------------
% 0.22/0.50  % (10651)------------------------------
% 0.22/0.51  % (10659)Refutation not found, incomplete strategy% (10659)------------------------------
% 0.22/0.51  % (10659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10659)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (10659)Memory used [KB]: 10618
% 0.22/0.51  % (10659)Time elapsed: 0.094 s
% 0.22/0.51  % (10659)------------------------------
% 0.22/0.51  % (10659)------------------------------
% 0.22/0.51  % (10667)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.51  % (10658)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (10667)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f27,f32,f95,f124,f133,f135,f139,f140,f197])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl2_10 | ~spl2_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f196,f54,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl2_10 <=> k1_xboole_0 = sK0),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    spl2_6 <=> k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | ~spl2_6),
% 0.22/0.51    inference(subsumption_resolution,[],[f183,f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_6),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f182])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_6),
% 0.22/0.51    inference(superposition,[],[f14,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | ~spl2_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f54])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ~spl2_10 | spl2_1 | ~spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f137,f38,f24,f89])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    spl2_1 <=> sK0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    spl2_3 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    k1_xboole_0 != sK0 | (spl2_1 | ~spl2_3)),
% 0.22/0.51    inference(backward_demodulation,[],[f26,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f38])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    sK0 != sK1 | spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f24])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    spl2_6 | ~spl2_2 | ~spl2_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f138,f38,f29,f54])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    spl2_2 <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | (~spl2_2 | ~spl2_3)),
% 0.22/0.51    inference(forward_demodulation,[],[f136,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl2_2 | ~spl2_3)),
% 0.22/0.51    inference(backward_demodulation,[],[f31,f40])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f29])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    spl2_3 | ~spl2_6 | ~spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f134,f29,f54,f38])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK1 | ~spl2_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f129,f14])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | ~spl2_2),
% 0.22/0.51    inference(superposition,[],[f14,f31])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    spl2_3 | spl2_5 | ~spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f132,f29,f48,f38])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl2_5 <=> sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) | k1_xboole_0 = sK1 | ~spl2_2),
% 0.22/0.51    inference(subsumption_resolution,[],[f128,f14])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK1,sK1) | ~spl2_2),
% 0.22/0.51    inference(superposition,[],[f18,f31])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    spl2_6 | ~spl2_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f123])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    $false | (spl2_6 | ~spl2_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f108,f21])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (spl2_6 | ~spl2_10)),
% 0.22/0.51    inference(backward_demodulation,[],[f56,f91])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | ~spl2_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f89])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) | spl2_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f54])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl2_10 | spl2_1 | ~spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f94,f48,f24,f89])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | (spl2_1 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f93,f14])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | (spl2_1 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f85,f26])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    sK0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(sK0,sK0) | ~spl2_5),
% 0.22/0.51    inference(superposition,[],[f18,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    sK1 = k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)) | ~spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f48])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    spl2_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f29])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0) = k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)),
% 0.22/0.51    inference(definition_unfolding,[],[f12,f19,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    sK0 != sK1 & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1)) => (sK0 != sK1 & k3_zfmisc_1(sK0,sK0,sK0) = k3_zfmisc_1(sK1,sK1,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ? [X0,X1] : (X0 != X1 & k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.22/0.51    inference(negated_conjecture,[],[f4])).
% 0.22/0.51  fof(f4,conjecture,(
% 0.22/0.51    ! [X0,X1] : (k3_zfmisc_1(X0,X0,X0) = k3_zfmisc_1(X1,X1,X1) => X0 = X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_mcart_1)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ~spl2_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f13,f24])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    sK0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (10667)------------------------------
% 0.22/0.51  % (10667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10667)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (10667)Memory used [KB]: 6268
% 0.22/0.51  % (10667)Time elapsed: 0.105 s
% 0.22/0.51  % (10667)------------------------------
% 0.22/0.51  % (10667)------------------------------
% 0.22/0.52  % (10641)Success in time 0.154 s
%------------------------------------------------------------------------------
