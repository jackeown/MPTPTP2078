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
% DateTime   : Thu Dec  3 12:55:29 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 153 expanded)
%              Number of leaves         :   20 (  60 expanded)
%              Depth                    :    7
%              Number of atoms          :  229 ( 370 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f61,f95,f99,f174,f190,f196,f199,f202,f205,f211,f213,f216,f221])).

fof(f221,plain,
    ( spl2_1
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl2_1
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f144,f55,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f29])).

fof(f29,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f55,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_1
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f144,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_11
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f216,plain,
    ( spl2_12
    | spl2_10
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f215,f86,f129,f151])).

fof(f151,plain,
    ( spl2_12
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f129,plain,
    ( spl2_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f86,plain,
    ( spl2_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f215,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl2_4 ),
    inference(resolution,[],[f88,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f88,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f213,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f212,f57,f90,f86,f82])).

fof(f82,plain,
    ( spl2_3
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f90,plain,
    ( spl2_5
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f57,plain,
    ( spl2_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f212,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f58,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f211,plain,
    ( ~ spl2_7
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f112,f144,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f112,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl2_7
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f205,plain,
    ( spl2_11
    | spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f203,f53,f129,f142])).

fof(f203,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f54,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f202,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_5
    | spl2_2 ),
    inference(avatar_split_clause,[],[f201,f57,f90,f82,f110])).

fof(f201,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | spl2_2 ),
    inference(resolution,[],[f59,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f59,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f199,plain,
    ( spl2_11
    | ~ spl2_13
    | ~ spl2_5
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f197,f151,f90,f178,f142])).

fof(f178,plain,
    ( spl2_13
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f197,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl2_12 ),
    inference(resolution,[],[f153,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f153,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f151])).

fof(f196,plain,
    ( spl2_1
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl2_1
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f46,f186])).

fof(f186,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))
    | spl2_1
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f55,f131])).

fof(f131,plain,
    ( sK0 = sK1
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f46,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f190,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f187])).

fof(f187,plain,
    ( $false
    | spl2_13 ),
    inference(subsumption_resolution,[],[f63,f180])).

fof(f180,plain,
    ( ~ v1_ordinal1(sK0)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f178])).

fof(f63,plain,(
    v1_ordinal1(sK0) ),
    inference(resolution,[],[f31,f27])).

fof(f27,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f174,plain,
    ( ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f161,f161,f34])).

fof(f161,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(superposition,[],[f112,f131])).

fof(f99,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f26,f92])).

fof(f92,plain,
    ( ~ v3_ordinal1(sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f26,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f27,f84])).

fof(f84,plain,
    ( ~ v3_ordinal1(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f61,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f45,f57,f53])).

fof(f45,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f24,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f44,f57,f53])).

fof(f44,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f25,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (29864)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (29848)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (29835)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (29864)Refutation not found, incomplete strategy% (29864)------------------------------
% 0.21/0.51  % (29864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29864)Memory used [KB]: 1663
% 0.21/0.51  % (29864)Time elapsed: 0.057 s
% 0.21/0.51  % (29864)------------------------------
% 0.21/0.51  % (29864)------------------------------
% 1.21/0.51  % (29840)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.21/0.51  % (29848)Refutation found. Thanks to Tanya!
% 1.21/0.51  % SZS status Theorem for theBenchmark
% 1.21/0.51  % SZS output start Proof for theBenchmark
% 1.21/0.51  fof(f222,plain,(
% 1.21/0.51    $false),
% 1.21/0.51    inference(avatar_sat_refutation,[],[f60,f61,f95,f99,f174,f190,f196,f199,f202,f205,f211,f213,f216,f221])).
% 1.21/0.51  fof(f221,plain,(
% 1.21/0.51    spl2_1 | ~spl2_11),
% 1.21/0.51    inference(avatar_contradiction_clause,[],[f219])).
% 1.21/0.51  fof(f219,plain,(
% 1.21/0.51    $false | (spl2_1 | ~spl2_11)),
% 1.21/0.51    inference(unit_resulting_resolution,[],[f144,f55,f48])).
% 1.21/0.51  fof(f48,plain,(
% 1.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 1.21/0.51    inference(definition_unfolding,[],[f42,f29])).
% 1.21/0.51  fof(f29,plain,(
% 1.21/0.51    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.21/0.51    inference(cnf_transformation,[],[f5])).
% 1.21/0.51  fof(f5,axiom,(
% 1.21/0.51    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.21/0.51  fof(f42,plain,(
% 1.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.21/0.51    inference(cnf_transformation,[],[f8])).
% 1.21/0.51  fof(f8,axiom,(
% 1.21/0.51    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.21/0.51  fof(f55,plain,(
% 1.21/0.51    ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | spl2_1),
% 1.21/0.51    inference(avatar_component_clause,[],[f53])).
% 1.21/0.51  fof(f53,plain,(
% 1.21/0.51    spl2_1 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.21/0.52  fof(f144,plain,(
% 1.21/0.52    r2_hidden(sK0,sK1) | ~spl2_11),
% 1.21/0.52    inference(avatar_component_clause,[],[f142])).
% 1.21/0.52  fof(f142,plain,(
% 1.21/0.52    spl2_11 <=> r2_hidden(sK0,sK1)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.21/0.52  fof(f216,plain,(
% 1.21/0.52    spl2_12 | spl2_10 | ~spl2_4),
% 1.21/0.52    inference(avatar_split_clause,[],[f215,f86,f129,f151])).
% 1.21/0.52  fof(f151,plain,(
% 1.21/0.52    spl2_12 <=> r2_xboole_0(sK0,sK1)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.21/0.52  fof(f129,plain,(
% 1.21/0.52    spl2_10 <=> sK0 = sK1),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.21/0.52  fof(f86,plain,(
% 1.21/0.52    spl2_4 <=> r1_tarski(sK0,sK1)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.21/0.52  fof(f215,plain,(
% 1.21/0.52    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl2_4),
% 1.21/0.52    inference(resolution,[],[f88,f40])).
% 1.21/0.52  fof(f40,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f2])).
% 1.21/0.52  fof(f2,axiom,(
% 1.21/0.52    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.21/0.52  fof(f88,plain,(
% 1.21/0.52    r1_tarski(sK0,sK1) | ~spl2_4),
% 1.21/0.52    inference(avatar_component_clause,[],[f86])).
% 1.21/0.52  fof(f213,plain,(
% 1.21/0.52    ~spl2_3 | spl2_4 | ~spl2_5 | ~spl2_2),
% 1.21/0.52    inference(avatar_split_clause,[],[f212,f57,f90,f86,f82])).
% 1.21/0.52  fof(f82,plain,(
% 1.21/0.52    spl2_3 <=> v3_ordinal1(sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.21/0.52  fof(f90,plain,(
% 1.21/0.52    spl2_5 <=> v3_ordinal1(sK1)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.21/0.52  fof(f57,plain,(
% 1.21/0.52    spl2_2 <=> r1_ordinal1(sK0,sK1)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.21/0.52  fof(f212,plain,(
% 1.21/0.52    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~spl2_2),
% 1.21/0.52    inference(resolution,[],[f58,f37])).
% 1.21/0.52  fof(f37,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f23])).
% 1.21/0.52  fof(f23,plain,(
% 1.21/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.21/0.52    inference(flattening,[],[f22])).
% 1.21/0.52  fof(f22,plain,(
% 1.21/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.21/0.52    inference(ennf_transformation,[],[f6])).
% 1.21/0.52  fof(f6,axiom,(
% 1.21/0.52    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.21/0.52  fof(f58,plain,(
% 1.21/0.52    r1_ordinal1(sK0,sK1) | ~spl2_2),
% 1.21/0.52    inference(avatar_component_clause,[],[f57])).
% 1.21/0.52  fof(f211,plain,(
% 1.21/0.52    ~spl2_7 | ~spl2_11),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f208])).
% 1.21/0.52  fof(f208,plain,(
% 1.21/0.52    $false | (~spl2_7 | ~spl2_11)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f112,f144,f34])).
% 1.21/0.52  fof(f34,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f19])).
% 1.21/0.52  fof(f19,plain,(
% 1.21/0.52    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.21/0.52    inference(ennf_transformation,[],[f1])).
% 1.21/0.52  fof(f1,axiom,(
% 1.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.21/0.52  fof(f112,plain,(
% 1.21/0.52    r2_hidden(sK1,sK0) | ~spl2_7),
% 1.21/0.52    inference(avatar_component_clause,[],[f110])).
% 1.21/0.52  fof(f110,plain,(
% 1.21/0.52    spl2_7 <=> r2_hidden(sK1,sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.21/0.52  fof(f205,plain,(
% 1.21/0.52    spl2_11 | spl2_10 | ~spl2_1),
% 1.21/0.52    inference(avatar_split_clause,[],[f203,f53,f129,f142])).
% 1.21/0.52  fof(f203,plain,(
% 1.21/0.52    sK0 = sK1 | r2_hidden(sK0,sK1) | ~spl2_1),
% 1.21/0.52    inference(resolution,[],[f54,f49])).
% 1.21/0.52  fof(f49,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 = X1 | r2_hidden(X0,X1)) )),
% 1.21/0.52    inference(definition_unfolding,[],[f41,f29])).
% 1.21/0.52  fof(f41,plain,(
% 1.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.21/0.52    inference(cnf_transformation,[],[f8])).
% 1.21/0.52  fof(f54,plain,(
% 1.21/0.52    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl2_1),
% 1.21/0.52    inference(avatar_component_clause,[],[f53])).
% 1.21/0.52  fof(f202,plain,(
% 1.21/0.52    spl2_7 | ~spl2_3 | ~spl2_5 | spl2_2),
% 1.21/0.52    inference(avatar_split_clause,[],[f201,f57,f90,f82,f110])).
% 1.21/0.52  fof(f201,plain,(
% 1.21/0.52    ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | spl2_2),
% 1.21/0.52    inference(resolution,[],[f59,f33])).
% 1.21/0.52  fof(f33,plain,(
% 1.21/0.52    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f18])).
% 1.21/0.52  fof(f18,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.21/0.52    inference(flattening,[],[f17])).
% 1.21/0.52  fof(f17,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f10])).
% 1.21/0.52  fof(f10,axiom,(
% 1.21/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.21/0.52  fof(f59,plain,(
% 1.21/0.52    ~r1_ordinal1(sK0,sK1) | spl2_2),
% 1.21/0.52    inference(avatar_component_clause,[],[f57])).
% 1.21/0.52  fof(f199,plain,(
% 1.21/0.52    spl2_11 | ~spl2_13 | ~spl2_5 | ~spl2_12),
% 1.21/0.52    inference(avatar_split_clause,[],[f197,f151,f90,f178,f142])).
% 1.21/0.52  fof(f178,plain,(
% 1.21/0.52    spl2_13 <=> v1_ordinal1(sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.21/0.52  fof(f197,plain,(
% 1.21/0.52    ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0) | r2_hidden(sK0,sK1) | ~spl2_12),
% 1.21/0.52    inference(resolution,[],[f153,f30])).
% 1.21/0.52  fof(f30,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0) | r2_hidden(X0,X1)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f15])).
% 1.21/0.52  fof(f15,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.21/0.52    inference(flattening,[],[f14])).
% 1.21/0.52  fof(f14,plain,(
% 1.21/0.52    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f9])).
% 1.21/0.52  fof(f9,axiom,(
% 1.21/0.52    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 1.21/0.52  fof(f153,plain,(
% 1.21/0.52    r2_xboole_0(sK0,sK1) | ~spl2_12),
% 1.21/0.52    inference(avatar_component_clause,[],[f151])).
% 1.21/0.52  fof(f196,plain,(
% 1.21/0.52    spl2_1 | ~spl2_10),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f192])).
% 1.21/0.52  fof(f192,plain,(
% 1.21/0.52    $false | (spl2_1 | ~spl2_10)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f46,f186])).
% 1.21/0.52  fof(f186,plain,(
% 1.21/0.52    ~r2_hidden(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) | (spl2_1 | ~spl2_10)),
% 1.21/0.52    inference(forward_demodulation,[],[f55,f131])).
% 1.21/0.52  fof(f131,plain,(
% 1.21/0.52    sK0 = sK1 | ~spl2_10),
% 1.21/0.52    inference(avatar_component_clause,[],[f129])).
% 1.21/0.52  fof(f46,plain,(
% 1.21/0.52    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 1.21/0.52    inference(definition_unfolding,[],[f28,f29])).
% 1.21/0.52  fof(f28,plain,(
% 1.21/0.52    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 1.21/0.52    inference(cnf_transformation,[],[f7])).
% 1.21/0.52  fof(f7,axiom,(
% 1.21/0.52    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 1.21/0.52  fof(f190,plain,(
% 1.21/0.52    spl2_13),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f187])).
% 1.21/0.52  fof(f187,plain,(
% 1.21/0.52    $false | spl2_13),
% 1.21/0.52    inference(subsumption_resolution,[],[f63,f180])).
% 1.21/0.52  fof(f180,plain,(
% 1.21/0.52    ~v1_ordinal1(sK0) | spl2_13),
% 1.21/0.52    inference(avatar_component_clause,[],[f178])).
% 1.21/0.52  fof(f63,plain,(
% 1.21/0.52    v1_ordinal1(sK0)),
% 1.21/0.52    inference(resolution,[],[f31,f27])).
% 1.21/0.52  fof(f27,plain,(
% 1.21/0.52    v3_ordinal1(sK0)),
% 1.21/0.52    inference(cnf_transformation,[],[f13])).
% 1.21/0.52  fof(f13,plain,(
% 1.21/0.52    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f12])).
% 1.21/0.52  fof(f12,negated_conjecture,(
% 1.21/0.52    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.21/0.52    inference(negated_conjecture,[],[f11])).
% 1.21/0.52  fof(f11,conjecture,(
% 1.21/0.52    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.21/0.52  fof(f31,plain,(
% 1.21/0.52    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f16])).
% 1.21/0.52  fof(f16,plain,(
% 1.21/0.52    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f3])).
% 1.21/0.52  fof(f3,axiom,(
% 1.21/0.52    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 1.21/0.52  fof(f174,plain,(
% 1.21/0.52    ~spl2_7 | ~spl2_10),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f171])).
% 1.21/0.52  fof(f171,plain,(
% 1.21/0.52    $false | (~spl2_7 | ~spl2_10)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f161,f161,f34])).
% 1.21/0.52  fof(f161,plain,(
% 1.21/0.52    r2_hidden(sK0,sK0) | (~spl2_7 | ~spl2_10)),
% 1.21/0.52    inference(superposition,[],[f112,f131])).
% 1.21/0.52  fof(f99,plain,(
% 1.21/0.52    spl2_5),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f98])).
% 1.21/0.52  fof(f98,plain,(
% 1.21/0.52    $false | spl2_5),
% 1.21/0.52    inference(subsumption_resolution,[],[f26,f92])).
% 1.21/0.52  fof(f92,plain,(
% 1.21/0.52    ~v3_ordinal1(sK1) | spl2_5),
% 1.21/0.52    inference(avatar_component_clause,[],[f90])).
% 1.21/0.52  fof(f26,plain,(
% 1.21/0.52    v3_ordinal1(sK1)),
% 1.21/0.52    inference(cnf_transformation,[],[f13])).
% 1.21/0.52  fof(f95,plain,(
% 1.21/0.52    spl2_3),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f94])).
% 1.21/0.52  fof(f94,plain,(
% 1.21/0.52    $false | spl2_3),
% 1.21/0.52    inference(subsumption_resolution,[],[f27,f84])).
% 1.21/0.52  fof(f84,plain,(
% 1.21/0.52    ~v3_ordinal1(sK0) | spl2_3),
% 1.21/0.52    inference(avatar_component_clause,[],[f82])).
% 1.21/0.52  fof(f61,plain,(
% 1.21/0.52    spl2_1 | spl2_2),
% 1.21/0.52    inference(avatar_split_clause,[],[f45,f57,f53])).
% 1.21/0.52  fof(f45,plain,(
% 1.21/0.52    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.21/0.52    inference(definition_unfolding,[],[f24,f29])).
% 1.21/0.52  fof(f24,plain,(
% 1.21/0.52    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.21/0.52    inference(cnf_transformation,[],[f13])).
% 1.21/0.52  fof(f60,plain,(
% 1.21/0.52    ~spl2_1 | ~spl2_2),
% 1.21/0.52    inference(avatar_split_clause,[],[f44,f57,f53])).
% 1.21/0.52  fof(f44,plain,(
% 1.21/0.52    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 1.21/0.52    inference(definition_unfolding,[],[f25,f29])).
% 1.21/0.52  fof(f25,plain,(
% 1.21/0.52    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.21/0.52    inference(cnf_transformation,[],[f13])).
% 1.21/0.52  % SZS output end Proof for theBenchmark
% 1.21/0.52  % (29848)------------------------------
% 1.21/0.52  % (29848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (29848)Termination reason: Refutation
% 1.21/0.52  
% 1.21/0.52  % (29848)Memory used [KB]: 6268
% 1.21/0.52  % (29848)Time elapsed: 0.064 s
% 1.21/0.52  % (29848)------------------------------
% 1.21/0.52  % (29848)------------------------------
% 1.21/0.52  % (29834)Success in time 0.16 s
%------------------------------------------------------------------------------
