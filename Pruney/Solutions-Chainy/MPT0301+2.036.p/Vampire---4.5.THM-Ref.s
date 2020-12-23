%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 125 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :    6
%              Number of atoms          :  232 ( 345 expanded)
%              Number of equality atoms :   47 (  83 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f51,f55,f61,f70,f82,f96,f100,f119,f123,f146,f154,f165,f177,f180,f193])).

fof(f193,plain,
    ( spl9_2
    | ~ spl9_8
    | ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl9_2
    | ~ spl9_8
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f184,f43])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | spl9_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f184,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_8
    | ~ spl9_24 ),
    inference(resolution,[],[f164,f69])).

fof(f69,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl9_8
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK2(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f164,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl9_24
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f180,plain,
    ( spl9_3
    | ~ spl9_15
    | ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl9_3
    | ~ spl9_15
    | ~ spl9_21 ),
    inference(unit_resulting_resolution,[],[f47,f99,f99,f153])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK7(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 )
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl9_21
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK7(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X2)
        | k2_zfmisc_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f99,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_15
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f47,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl9_3
  <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f177,plain,
    ( spl9_4
    | ~ spl9_8
    | ~ spl9_23 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl9_4
    | ~ spl9_8
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f170,f50])).

fof(f50,plain,
    ( k1_xboole_0 != sK0
    | spl9_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl9_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f170,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_8
    | ~ spl9_23 ),
    inference(resolution,[],[f161,f69])).

fof(f161,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl9_23
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f165,plain,
    ( spl9_23
    | spl9_24
    | ~ spl9_6
    | ~ spl9_15
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f150,f117,f98,f57,f163,f160])).

fof(f57,plain,
    ( spl9_6
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f117,plain,
    ( spl9_18
  <=> ! [X1,X5,X0,X4] :
        ( ~ r2_hidden(X4,X0)
        | ~ r2_hidden(X5,X1)
        | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_6
    | ~ spl9_15
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f147,f99])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k1_xboole_0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(superposition,[],[f118,f58])).

fof(f58,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f118,plain,
    ( ! [X4,X0,X5,X1] :
        ( r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))
        | ~ r2_hidden(X5,X1)
        | ~ r2_hidden(X4,X0) )
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f154,plain,(
    spl9_21 ),
    inference(avatar_split_clause,[],[f21,f152])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f146,plain,
    ( spl9_1
    | ~ spl9_8
    | ~ spl9_19 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl9_1
    | ~ spl9_8
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f40,f132])).

fof(f132,plain,
    ( ! [X3] : k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0)
    | ~ spl9_8
    | ~ spl9_19 ),
    inference(resolution,[],[f122,f69])).

% (21296)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f122,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl9_19
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f40,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl9_1
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f123,plain,
    ( spl9_19
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f112,f98,f94,f121])).

fof(f94,plain,
    ( spl9_14
  <=> ! [X1,X3,X0] :
        ( r2_hidden(sK6(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f112,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))
    | ~ spl9_14
    | ~ spl9_15 ),
    inference(resolution,[],[f95,f99])).

fof(f95,plain,
    ( ! [X0,X3,X1] :
        ( r2_hidden(sK6(X0,X1,X3),X1)
        | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f119,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f32,f117])).

fof(f32,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f100,plain,
    ( spl9_15
    | ~ spl9_5
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f92,f80,f53,f98])).

fof(f53,plain,
    ( spl9_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f80,plain,
    ( spl9_11
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f92,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl9_5
    | ~ spl9_11 ),
    inference(condensation,[],[f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl9_5
    | ~ spl9_11 ),
    inference(resolution,[],[f81,f54])).

fof(f54,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f96,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f34,f94])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f17,f80])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f70,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f16,f68])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f61,plain,
    ( spl9_6
    | spl9_2
    | spl9_4 ),
    inference(avatar_split_clause,[],[f14,f49,f42,f57])).

fof(f14,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f55,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f15,f53])).

fof(f15,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

% (21313)Refutation not found, incomplete strategy% (21313)------------------------------
% (21313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f51,plain,
    ( ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f37,f49,f46])).

fof(f37,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(inner_rewriting,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f36,f42,f39])).

fof(f36,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f13])).

fof(f13,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:16:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (21309)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (21301)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (21310)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (21302)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (21303)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (21303)Refutation not found, incomplete strategy% (21303)------------------------------
% 0.21/0.50  % (21303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21303)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21303)Memory used [KB]: 6012
% 0.21/0.50  % (21303)Time elapsed: 0.070 s
% 0.21/0.50  % (21303)------------------------------
% 0.21/0.50  % (21303)------------------------------
% 0.21/0.50  % (21308)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (21293)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (21293)Refutation not found, incomplete strategy% (21293)------------------------------
% 0.21/0.50  % (21293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21293)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21293)Memory used [KB]: 6140
% 0.21/0.50  % (21293)Time elapsed: 0.080 s
% 0.21/0.50  % (21293)------------------------------
% 0.21/0.50  % (21293)------------------------------
% 0.21/0.50  % (21307)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (21295)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (21306)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (21298)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (21294)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21300)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (21305)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21294)Refutation not found, incomplete strategy% (21294)------------------------------
% 0.21/0.51  % (21294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21294)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21294)Memory used [KB]: 10618
% 0.21/0.51  % (21294)Time elapsed: 0.060 s
% 0.21/0.51  % (21294)------------------------------
% 0.21/0.51  % (21294)------------------------------
% 0.21/0.51  % (21297)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (21313)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (21302)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f44,f51,f55,f61,f70,f82,f96,f100,f119,f123,f146,f154,f165,f177,f180,f193])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    spl9_2 | ~spl9_8 | ~spl9_24),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    $false | (spl9_2 | ~spl9_8 | ~spl9_24)),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | spl9_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    spl9_2 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | (~spl9_8 | ~spl9_24)),
% 0.21/0.51    inference(resolution,[],[f164,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) ) | ~spl9_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl9_8 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl9_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl9_24 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl9_3 | ~spl9_15 | ~spl9_21),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    $false | (spl9_3 | ~spl9_15 | ~spl9_21)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f47,f99,f99,f153])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) ) | ~spl9_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f152])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl9_21 <=> ! [X1,X0,X2] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl9_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl9_15 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) | spl9_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl9_3 <=> k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    spl9_4 | ~spl9_8 | ~spl9_23),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    $false | (spl9_4 | ~spl9_8 | ~spl9_23)),
% 0.21/0.51    inference(subsumption_resolution,[],[f170,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | spl9_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    spl9_4 <=> k1_xboole_0 = sK0),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | (~spl9_8 | ~spl9_23)),
% 0.21/0.51    inference(resolution,[],[f161,f69])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl9_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl9_23 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl9_23 | spl9_24 | ~spl9_6 | ~spl9_15 | ~spl9_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f150,f117,f98,f57,f163,f160])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl9_6 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl9_18 <=> ! [X1,X5,X0,X4] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl9_6 | ~spl9_15 | ~spl9_18)),
% 0.21/0.51    inference(subsumption_resolution,[],[f147,f99])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl9_6 | ~spl9_18)),
% 0.21/0.51    inference(superposition,[],[f118,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl9_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f57])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) ) | ~spl9_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f117])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    spl9_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f21,f152])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    spl9_1 | ~spl9_8 | ~spl9_19),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    $false | (spl9_1 | ~spl9_8 | ~spl9_19)),
% 0.21/0.51    inference(subsumption_resolution,[],[f40,f132])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0)) ) | (~spl9_8 | ~spl9_19)),
% 0.21/0.51    inference(resolution,[],[f122,f69])).
% 0.21/0.51  % (21296)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) ) | ~spl9_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl9_19 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | spl9_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    spl9_1 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl9_19 | ~spl9_14 | ~spl9_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f112,f98,f94,f121])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl9_14 <=> ! [X1,X3,X0] : (r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0))) ) | (~spl9_14 | ~spl9_15)),
% 0.21/0.51    inference(resolution,[],[f95,f99])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) ) | ~spl9_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f94])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl9_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f117])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.51    inference(equality_resolution,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl9_15 | ~spl9_5 | ~spl9_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f92,f80,f53,f98])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl9_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl9_11 <=> ! [X1,X0,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl9_5 | ~spl9_11)),
% 0.21/0.51    inference(condensation,[],[f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) ) | (~spl9_5 | ~spl9_11)),
% 0.21/0.51    inference(resolution,[],[f81,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl9_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f53])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) ) | ~spl9_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl9_14),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f94])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl9_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f17,f80])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl9_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f16,f68])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl9_6 | spl9_2 | spl9_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f14,f49,f42,f57])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl9_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f15,f53])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.51  % (21313)Refutation not found, incomplete strategy% (21313)------------------------------
% 0.21/0.51  % (21313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ~spl9_3 | ~spl9_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f37,f49,f46])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.21/0.51    inference(inner_rewriting,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    k1_xboole_0 != sK0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ~spl9_1 | ~spl9_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f42,f39])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)),
% 0.21/0.51    inference(inner_rewriting,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (21302)------------------------------
% 0.21/0.51  % (21302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21302)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (21302)Memory used [KB]: 10618
% 0.21/0.51  % (21302)Time elapsed: 0.063 s
% 0.21/0.51  % (21302)------------------------------
% 0.21/0.51  % (21302)------------------------------
% 0.21/0.51  % (21292)Success in time 0.151 s
%------------------------------------------------------------------------------
