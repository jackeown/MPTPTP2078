%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 125 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  161 ( 333 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f46,f132,f155,f179,f188,f221,f239])).

fof(f239,plain,
    ( spl4_1
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl4_1
    | ~ spl4_10 ),
    inference(resolution,[],[f110,f31])).

fof(f31,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f110,plain,
    ( ! [X0,X1] : r1_tarski(X0,X1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_10
  <=> ! [X1,X0] : r1_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f221,plain,
    ( spl4_2
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f219,f153,f106,f34])).

fof(f34,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f106,plain,
    ( spl4_9
  <=> ! [X3,X2] :
        ( r1_tarski(k1_xboole_0,X2)
        | r2_hidden(sK3(k1_xboole_0,X2),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f153,plain,
    ( spl4_15
  <=> ! [X2] : r1_tarski(sK0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f219,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_9
    | ~ spl4_15 ),
    inference(resolution,[],[f215,f196])).

fof(f196,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK0)
        | sK0 = X2 )
    | ~ spl4_15 ),
    inference(resolution,[],[f154,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f154,plain,
    ( ! [X2] : r1_tarski(sK0,X2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f153])).

fof(f215,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,
    ( ! [X0] :
        ( r1_tarski(k1_xboole_0,X0)
        | r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_9 ),
    inference(resolution,[],[f107,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f107,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(k1_xboole_0,X2),X3)
        | r1_tarski(k1_xboole_0,X2) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f188,plain,
    ( spl4_1
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f187,f150,f29])).

fof(f150,plain,
    ( spl4_14
  <=> ! [X3] :
        ( r1_tarski(sK1,X3)
        | r2_hidden(sK3(sK1,X3),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f187,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ spl4_14 ),
    inference(resolution,[],[f151,f17])).

fof(f151,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(sK1,X3),sK2)
        | r1_tarski(sK1,X3) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f179,plain,
    ( spl4_15
    | spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f174,f39,f150,f153])).

fof(f39,plain,
    ( spl4_3
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK1,X0)
        | r1_tarski(sK0,X1)
        | r2_hidden(sK3(sK1,X0),sK2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f156,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f156,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK3(sK0,X1),sK3(sK1,X0)),k2_zfmisc_1(sK0,sK2))
        | r1_tarski(sK1,X0)
        | r1_tarski(sK0,X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f41,f96])).

fof(f96,plain,(
    ! [X24,X23,X21,X22,X20] :
      ( ~ r1_tarski(k2_zfmisc_1(X20,X22),X24)
      | r1_tarski(X22,X23)
      | r2_hidden(k4_tarski(sK3(X20,X21),sK3(X22,X23)),X24)
      | r1_tarski(X20,X21) ) ),
    inference(resolution,[],[f88,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK3(X2,X3)),k2_zfmisc_1(X0,X2))
      | r1_tarski(X0,X1)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f83,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK3(X2,X3),X0),k2_zfmisc_1(X2,X1))
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f23,f16])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f155,plain,
    ( spl4_14
    | spl4_15
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f145,f43,f153,f150])).

fof(f43,plain,
    ( spl4_4
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f145,plain,
    ( ! [X2,X3] :
        ( r1_tarski(sK0,X2)
        | r1_tarski(sK1,X3)
        | r2_hidden(sK3(sK1,X3),sK2) )
    | ~ spl4_4 ),
    inference(resolution,[],[f140,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK3(sK1,X1),sK3(sK0,X0)),k2_zfmisc_1(sK2,sK0))
        | r1_tarski(sK0,X0)
        | r1_tarski(sK1,X1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f96,f45])).

fof(f45,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f132,plain,
    ( spl4_10
    | spl4_9 ),
    inference(avatar_split_clause,[],[f123,f106,f109])).

fof(f123,plain,(
    ! [X10,X8,X7,X9] :
      ( r1_tarski(k1_xboole_0,X7)
      | r1_tarski(X8,X9)
      | r2_hidden(sK3(k1_xboole_0,X7),X10) ) ),
    inference(resolution,[],[f98,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f21,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f98,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k4_tarski(sK3(k1_xboole_0,X4),sK3(X3,X5)),k1_xboole_0)
      | r1_tarski(k1_xboole_0,X4)
      | r1_tarski(X3,X5) ) ),
    inference(superposition,[],[f88,f27])).

fof(f27,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f9,f43,f39])).

fof(f9,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X1,X2)
      & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_tarski(X1,X2)
          & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
            | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f37,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f10,f34])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f11,f29])).

fof(f11,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:05:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (25504)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.49  % (25519)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.49  % (25496)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.49  % (25498)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (25506)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.50  % (25498)Refutation not found, incomplete strategy% (25498)------------------------------
% 0.21/0.50  % (25498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25498)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (25498)Memory used [KB]: 10618
% 0.21/0.50  % (25498)Time elapsed: 0.090 s
% 0.21/0.50  % (25498)------------------------------
% 0.21/0.50  % (25498)------------------------------
% 0.21/0.50  % (25512)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (25512)Refutation not found, incomplete strategy% (25512)------------------------------
% 0.21/0.50  % (25512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25491)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (25512)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25512)Memory used [KB]: 10746
% 0.21/0.51  % (25512)Time elapsed: 0.092 s
% 0.21/0.51  % (25512)------------------------------
% 0.21/0.51  % (25512)------------------------------
% 0.21/0.51  % (25517)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (25507)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (25514)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (25507)Refutation not found, incomplete strategy% (25507)------------------------------
% 0.21/0.51  % (25507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25507)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25507)Memory used [KB]: 10618
% 0.21/0.51  % (25507)Time elapsed: 0.107 s
% 0.21/0.51  % (25507)------------------------------
% 0.21/0.51  % (25507)------------------------------
% 0.21/0.51  % (25516)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.52  % (25499)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (25510)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (25501)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (25506)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f32,f37,f46,f132,f155,f179,f188,f221,f239])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    spl4_1 | ~spl4_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    $false | (spl4_1 | ~spl4_10)),
% 0.21/0.52    inference(resolution,[],[f110,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK2) | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    spl4_1 <=> r1_tarski(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1)) ) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    spl4_10 <=> ! [X1,X0] : r1_tarski(X0,X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    spl4_2 | ~spl4_9 | ~spl4_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f219,f153,f106,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    spl4_2 <=> k1_xboole_0 = sK0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl4_9 <=> ! [X3,X2] : (r1_tarski(k1_xboole_0,X2) | r2_hidden(sK3(k1_xboole_0,X2),X3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    spl4_15 <=> ! [X2] : r1_tarski(sK0,X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | (~spl4_9 | ~spl4_15)),
% 0.21/0.52    inference(resolution,[],[f215,f196])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ( ! [X2] : (~r1_tarski(X2,sK0) | sK0 = X2) ) | ~spl4_15),
% 0.21/0.52    inference(resolution,[],[f154,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ( ! [X2] : (r1_tarski(sK0,X2)) ) | ~spl4_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f153])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_9),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f210])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)) ) | ~spl4_9),
% 0.21/0.52    inference(resolution,[],[f107,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r2_hidden(sK3(k1_xboole_0,X2),X3) | r1_tarski(k1_xboole_0,X2)) ) | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f106])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    spl4_1 | ~spl4_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f187,f150,f29])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl4_14 <=> ! [X3] : (r1_tarski(sK1,X3) | r2_hidden(sK3(sK1,X3),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | ~spl4_14),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2) | ~spl4_14),
% 0.21/0.52    inference(resolution,[],[f151,f17])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(sK3(sK1,X3),sK2) | r1_tarski(sK1,X3)) ) | ~spl4_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f150])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    spl4_15 | spl4_14 | ~spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f174,f39,f150,f153])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl4_3 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(sK1,X0) | r1_tarski(sK0,X1) | r2_hidden(sK3(sK1,X0),sK2)) ) | ~spl4_3),
% 0.21/0.52    inference(resolution,[],[f156,f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(sK0,X1),sK3(sK1,X0)),k2_zfmisc_1(sK0,sK2)) | r1_tarski(sK1,X0) | r1_tarski(sK0,X1)) ) | ~spl4_3),
% 0.21/0.52    inference(resolution,[],[f41,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X24,X23,X21,X22,X20] : (~r1_tarski(k2_zfmisc_1(X20,X22),X24) | r1_tarski(X22,X23) | r2_hidden(k4_tarski(sK3(X20,X21),sK3(X22,X23)),X24) | r1_tarski(X20,X21)) )),
% 0.21/0.52    inference(resolution,[],[f88,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK3(X2,X3)),k2_zfmisc_1(X0,X2)) | r1_tarski(X0,X1) | r1_tarski(X2,X3)) )),
% 0.21/0.52    inference(resolution,[],[f83,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK3(X2,X3),X0),k2_zfmisc_1(X2,X1)) | r1_tarski(X2,X3)) )),
% 0.21/0.52    inference(resolution,[],[f23,f16])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2)) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    spl4_14 | spl4_15 | ~spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f145,f43,f153,f150])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    spl4_4 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r1_tarski(sK0,X2) | r1_tarski(sK1,X3) | r2_hidden(sK3(sK1,X3),sK2)) ) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f140,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(sK1,X1),sK3(sK0,X0)),k2_zfmisc_1(sK2,sK0)) | r1_tarski(sK0,X0) | r1_tarski(sK1,X1)) ) | ~spl4_4),
% 0.21/0.52    inference(resolution,[],[f96,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f43])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl4_10 | spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f123,f106,f109])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X10,X8,X7,X9] : (r1_tarski(k1_xboole_0,X7) | r1_tarski(X8,X9) | r2_hidden(sK3(k1_xboole_0,X7),X10)) )),
% 0.21/0.52    inference(resolution,[],[f98,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),k1_xboole_0) | r2_hidden(X1,X0)) )),
% 0.21/0.52    inference(superposition,[],[f21,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (r2_hidden(k4_tarski(sK3(k1_xboole_0,X4),sK3(X3,X5)),k1_xboole_0) | r1_tarski(k1_xboole_0,X4) | r1_tarski(X3,X5)) )),
% 0.21/0.52    inference(superposition,[],[f88,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    spl4_3 | spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f9,f43,f39])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK2,sK0)) | r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ~spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f10,f34])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ~spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f11,f29])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (25506)------------------------------
% 0.21/0.52  % (25506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25506)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (25506)Memory used [KB]: 10874
% 0.21/0.52  % (25506)Time elapsed: 0.101 s
% 0.21/0.52  % (25506)------------------------------
% 0.21/0.52  % (25506)------------------------------
% 0.21/0.52  % (25489)Success in time 0.152 s
%------------------------------------------------------------------------------
