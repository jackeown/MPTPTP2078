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
% DateTime   : Thu Dec  3 12:36:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 136 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  225 ( 588 expanded)
%              Number of equality atoms :  106 ( 347 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f70,f84,f96,f111,f124,f145,f157,f175])).

fof(f175,plain,
    ( spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | spl4_10
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f144,f42,f166])).

fof(f166,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_tarski(sK0,sK1))
        | sK1 = X2 )
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_tarski(sK0,sK1))
        | sK1 = X2
        | sK1 = X2 )
    | ~ spl4_12 ),
    inference(superposition,[],[f43,f156])).

fof(f156,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_12
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

% (17576)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f42,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f144,plain,
    ( sK0 != sK1
    | spl4_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f157,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f126,f121,f63,f154])).

fof(f63,plain,
    ( spl4_3
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f121,plain,
    ( spl4_9
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f126,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(superposition,[],[f65,f123])).

% (17577)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f123,plain,
    ( sK1 = sK2
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f65,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f145,plain,
    ( ~ spl4_10
    | spl4_1
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f128,f121,f47,f142])).

fof(f47,plain,
    ( spl4_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f128,plain,
    ( sK0 != sK1
    | spl4_1
    | ~ spl4_9 ),
    inference(superposition,[],[f49,f123])).

fof(f49,plain,
    ( sK0 != sK2
    | spl4_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f124,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f119,f107,f47,f121])).

fof(f107,plain,
    ( spl4_7
  <=> r2_hidden(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f119,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl4_7 ),
    inference(resolution,[],[f109,f43])).

fof(f109,plain,
    ( r2_hidden(sK2,k2_tarski(sK0,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f111,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f100,f63,f107])).

fof(f100,plain,
    ( r2_hidden(sK2,k2_tarski(sK0,sK1))
    | ~ spl4_3 ),
    inference(superposition,[],[f40,f65])).

fof(f40,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f96,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f33,f83,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f83,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_6
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f33,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f84,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f74,f67,f81])).

fof(f67,plain,
    ( spl4_4
  <=> k1_xboole_0 = k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl4_4 ),
    inference(superposition,[],[f40,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f70,plain,
    ( spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f59,f52,f67,f63])).

fof(f52,plain,
    ( spl4_2
  <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f59,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X1))
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f28,f31,f31])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f55,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f34,f52])).

fof(f34,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) ),
    inference(definition_unfolding,[],[f20,f31])).

fof(f20,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f50,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:00:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (17587)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (17579)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (17565)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (17571)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (17565)Refutation not found, incomplete strategy% (17565)------------------------------
% 0.21/0.51  % (17565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17565)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (17565)Memory used [KB]: 1663
% 0.21/0.51  % (17565)Time elapsed: 0.094 s
% 0.21/0.51  % (17565)------------------------------
% 0.21/0.51  % (17565)------------------------------
% 0.21/0.51  % (17587)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (17566)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (17564)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f50,f55,f70,f84,f96,f111,f124,f145,f157,f175])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    spl4_10 | ~spl4_12),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    $false | (spl4_10 | ~spl4_12)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f144,f42,f166])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X2] : (~r2_hidden(X2,k2_tarski(sK0,sK1)) | sK1 = X2) ) | ~spl4_12),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f159])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    ( ! [X2] : (~r2_hidden(X2,k2_tarski(sK0,sK1)) | sK1 = X2 | sK1 = X2) ) | ~spl4_12),
% 0.21/0.51    inference(superposition,[],[f43,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1) | ~spl4_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl4_12 <=> k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.51    inference(equality_resolution,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  % (17576)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.52    inference(rectify,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.21/0.52    inference(equality_resolution,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    sK0 != sK1 | spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f142])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl4_10 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    spl4_12 | ~spl4_3 | ~spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f126,f121,f63,f154])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl4_3 <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl4_9 <=> sK1 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    k2_tarski(sK0,sK1) = k2_tarski(sK1,sK1) | (~spl4_3 | ~spl4_9)),
% 0.21/0.52    inference(superposition,[],[f65,f123])).
% 0.21/0.52  % (17577)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    sK1 = sK2 | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ~spl4_10 | spl4_1 | ~spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f128,f121,f47,f142])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl4_1 <=> sK0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    sK0 != sK1 | (spl4_1 | ~spl4_9)),
% 0.21/0.52    inference(superposition,[],[f49,f123])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    sK0 != sK2 | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f47])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl4_9 | spl4_1 | ~spl4_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f119,f107,f47,f121])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl4_7 <=> r2_hidden(sK2,k2_tarski(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    sK0 = sK2 | sK1 = sK2 | ~spl4_7),
% 0.21/0.52    inference(resolution,[],[f109,f43])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    r2_hidden(sK2,k2_tarski(sK0,sK1)) | ~spl4_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f107])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    spl4_7 | ~spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f100,f63,f107])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    r2_hidden(sK2,k2_tarski(sK0,sK1)) | ~spl4_3),
% 0.21/0.52    inference(superposition,[],[f40,f65])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.21/0.52    inference(equality_resolution,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.21/0.52    inference(equality_resolution,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ~spl4_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    $false | ~spl4_6),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f33,f83,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    r2_hidden(sK1,k1_xboole_0) | ~spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl4_6 <=> r2_hidden(sK1,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl4_6 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f74,f67,f81])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl4_4 <=> k1_xboole_0 = k2_tarski(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    r2_hidden(sK1,k1_xboole_0) | ~spl4_4),
% 0.21/0.52    inference(superposition,[],[f40,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    k1_xboole_0 = k2_tarski(sK0,sK1) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f67])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl4_3 | spl4_4 | ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f59,f52,f67,f63])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl4_2 <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) | ~spl4_2),
% 0.21/0.52    inference(resolution,[],[f37,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f52])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X1)) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f31,f31])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f34,f52])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2))),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f31])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f47])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    sK0 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (17587)------------------------------
% 0.21/0.52  % (17587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17587)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (17587)Memory used [KB]: 10746
% 0.21/0.52  % (17587)Time elapsed: 0.064 s
% 0.21/0.52  % (17587)------------------------------
% 0.21/0.52  % (17587)------------------------------
% 0.21/0.52  % (17563)Success in time 0.161 s
%------------------------------------------------------------------------------
