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
% DateTime   : Thu Dec  3 12:41:09 EST 2020

% Result     : Theorem 6.85s
% Output     : Refutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 136 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 311 expanded)
%              Number of equality atoms :   46 (  96 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6786,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f62,f79,f80,f97,f175,f176,f177,f6785])).

fof(f6785,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f6784])).

fof(f6784,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f6770,f56])).

fof(f56,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f6770,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f6752,f84])).

fof(f84,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl4_3 ),
    inference(superposition,[],[f48,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_3
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f6752,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0)
        | k4_xboole_0(k1_tarski(sK0),sK1) = X0 )
    | ~ spl4_2 ),
    inference(duplicate_literal_removal,[],[f6718])).

fof(f6718,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0)
        | k4_xboole_0(k1_tarski(sK0),sK1) = X0
        | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0)
        | k4_xboole_0(k1_tarski(sK0),sK1) = X0 )
    | ~ spl4_2 ),
    inference(resolution,[],[f6084,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f6084,plain,
    ( ! [X6,X5] :
        ( r2_hidden(sK2(k1_tarski(sK0),X5,X6),sK1)
        | r2_hidden(sK2(k1_tarski(sK0),X5,X6),X6)
        | k4_xboole_0(k1_tarski(sK0),X5) = X6 )
    | ~ spl4_2 ),
    inference(resolution,[],[f6079,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f6079,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl4_2 ),
    inference(condensation,[],[f6067])).

fof(f6067,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f6060,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f6060,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k4_xboole_0(X5,sK1))
        | ~ r2_hidden(X6,k1_tarski(sK0)) )
    | ~ spl4_2 ),
    inference(superposition,[],[f48,f6047])).

fof(f6047,plain,
    ( ! [X13] : k4_xboole_0(X13,sK1) = k4_xboole_0(k4_xboole_0(X13,sK1),k1_tarski(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f89,f59])).

fof(f59,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f89,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,X4)
      | k4_xboole_0(X3,X4) = k4_xboole_0(k4_xboole_0(X3,X4),k1_tarski(X5)) ) ),
    inference(resolution,[],[f34,f48])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f177,plain,
    ( ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f101,f94,f58])).

fof(f94,plain,
    ( spl4_4
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f101,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK0,sK1)
    | ~ spl4_4 ),
    inference(superposition,[],[f35,f96])).

fof(f96,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f176,plain,
    ( ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f102,f94,f58])).

fof(f102,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f100,f52])).

fof(f52,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f100,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tarski(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl4_4 ),
    inference(superposition,[],[f48,f96])).

fof(f175,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f172,f52])).

fof(f172,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f171,f100])).

fof(f171,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k1_tarski(sK0)) )
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f160,f84])).

fof(f160,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k1_tarski(sK0)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f47,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f97,plain,
    ( spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f87,f58,f94])).

fof(f87,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK0))
    | spl4_2 ),
    inference(resolution,[],[f34,f60])).

fof(f60,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f80,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f74,f76])).

fof(f74,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f46,f65])).

fof(f65,plain,(
    ! [X6] : k5_xboole_0(k1_xboole_0,X6) = X6 ),
    inference(superposition,[],[f45,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f79,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f71,f76])).

fof(f71,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f65,f46])).

fof(f62,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f26,f58,f54])).

fof(f26,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f61,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f27,f58,f54])).

fof(f27,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:15:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (1359)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (1376)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (1370)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (1368)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (1377)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (1370)Refutation not found, incomplete strategy% (1370)------------------------------
% 0.20/0.52  % (1370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1358)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (1370)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (1370)Memory used [KB]: 10618
% 0.20/0.52  % (1370)Time elapsed: 0.058 s
% 0.20/0.52  % (1370)------------------------------
% 0.20/0.52  % (1370)------------------------------
% 0.20/0.52  % (1356)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (1371)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (1368)Refutation not found, incomplete strategy% (1368)------------------------------
% 0.20/0.53  % (1368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (1368)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (1368)Memory used [KB]: 1663
% 0.20/0.53  % (1368)Time elapsed: 0.116 s
% 0.20/0.53  % (1368)------------------------------
% 0.20/0.53  % (1368)------------------------------
% 0.20/0.53  % (1361)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (1353)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (1355)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (1357)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (1354)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (1362)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (1383)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (1383)Refutation not found, incomplete strategy% (1383)------------------------------
% 0.20/0.54  % (1383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (1383)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (1383)Memory used [KB]: 1663
% 0.20/0.54  % (1383)Time elapsed: 0.129 s
% 0.20/0.54  % (1383)------------------------------
% 0.20/0.54  % (1383)------------------------------
% 0.20/0.54  % (1380)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (1374)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (1381)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (1379)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (1372)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (1375)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (1382)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (1360)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.56  % (1364)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (1373)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.56  % (1367)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.56  % (1369)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.56  % (1365)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (1371)Refutation not found, incomplete strategy% (1371)------------------------------
% 0.20/0.56  % (1371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (1371)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (1371)Memory used [KB]: 1791
% 0.20/0.56  % (1371)Time elapsed: 0.147 s
% 0.20/0.56  % (1371)------------------------------
% 0.20/0.56  % (1371)------------------------------
% 0.20/0.56  % (1365)Refutation not found, incomplete strategy% (1365)------------------------------
% 0.20/0.56  % (1365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (1365)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (1365)Memory used [KB]: 6268
% 0.20/0.56  % (1365)Time elapsed: 0.149 s
% 0.20/0.56  % (1365)------------------------------
% 0.20/0.56  % (1365)------------------------------
% 0.20/0.56  % (1366)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.59  % (1378)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.07/0.65  % (1405)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.07/0.66  % (1356)Refutation not found, incomplete strategy% (1356)------------------------------
% 2.07/0.66  % (1356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.67  % (1356)Termination reason: Refutation not found, incomplete strategy
% 2.07/0.67  
% 2.07/0.67  % (1356)Memory used [KB]: 6140
% 2.07/0.67  % (1356)Time elapsed: 0.247 s
% 2.07/0.67  % (1356)------------------------------
% 2.07/0.67  % (1356)------------------------------
% 2.07/0.69  % (1407)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.07/0.70  % (1409)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.07/0.70  % (1408)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.62/0.71  % (1406)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.01/0.81  % (1410)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 3.01/0.83  % (1378)Time limit reached!
% 3.01/0.83  % (1378)------------------------------
% 3.01/0.83  % (1378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.01/0.83  % (1378)Termination reason: Time limit
% 3.01/0.83  
% 3.01/0.83  % (1378)Memory used [KB]: 13048
% 3.01/0.83  % (1378)Time elapsed: 0.415 s
% 3.01/0.83  % (1378)------------------------------
% 3.01/0.83  % (1378)------------------------------
% 3.71/0.86  % (1355)Time limit reached!
% 3.71/0.86  % (1355)------------------------------
% 3.71/0.86  % (1355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.71/0.86  % (1355)Termination reason: Time limit
% 3.71/0.86  
% 3.71/0.86  % (1355)Memory used [KB]: 6908
% 3.71/0.86  % (1355)Time elapsed: 0.446 s
% 3.71/0.86  % (1355)------------------------------
% 3.71/0.86  % (1355)------------------------------
% 4.37/0.94  % (1359)Time limit reached!
% 4.37/0.94  % (1359)------------------------------
% 4.37/0.94  % (1359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.37/0.96  % (1359)Termination reason: Time limit
% 4.37/0.96  % (1359)Termination phase: Saturation
% 4.37/0.96  
% 4.37/0.96  % (1359)Memory used [KB]: 15479
% 4.37/0.96  % (1359)Time elapsed: 0.543 s
% 4.37/0.96  % (1359)------------------------------
% 4.37/0.96  % (1359)------------------------------
% 4.37/0.97  % (1411)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.37/1.00  % (1412)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 4.81/1.04  % (1360)Time limit reached!
% 4.81/1.04  % (1360)------------------------------
% 4.81/1.04  % (1360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.81/1.04  % (1360)Termination reason: Time limit
% 4.81/1.04  
% 4.81/1.04  % (1360)Memory used [KB]: 7036
% 4.81/1.04  % (1360)Time elapsed: 0.631 s
% 4.81/1.04  % (1360)------------------------------
% 4.81/1.04  % (1360)------------------------------
% 5.24/1.14  % (1413)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.51/1.24  % (1414)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 6.51/1.24  % (1414)Refutation not found, incomplete strategy% (1414)------------------------------
% 6.51/1.24  % (1414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.51/1.24  % (1414)Termination reason: Refutation not found, incomplete strategy
% 6.51/1.24  
% 6.51/1.24  % (1414)Memory used [KB]: 10746
% 6.51/1.24  % (1414)Time elapsed: 0.146 s
% 6.51/1.24  % (1414)------------------------------
% 6.51/1.24  % (1414)------------------------------
% 6.85/1.24  % (1354)Time limit reached!
% 6.85/1.24  % (1354)------------------------------
% 6.85/1.24  % (1354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.85/1.24  % (1354)Termination reason: Time limit
% 6.85/1.24  
% 6.85/1.24  % (1354)Memory used [KB]: 3582
% 6.85/1.24  % (1354)Time elapsed: 0.814 s
% 6.85/1.24  % (1354)------------------------------
% 6.85/1.24  % (1354)------------------------------
% 6.85/1.31  % (1353)Refutation found. Thanks to Tanya!
% 6.85/1.31  % SZS status Theorem for theBenchmark
% 6.85/1.32  % SZS output start Proof for theBenchmark
% 6.85/1.32  fof(f6786,plain,(
% 6.85/1.32    $false),
% 6.85/1.32    inference(avatar_sat_refutation,[],[f61,f62,f79,f80,f97,f175,f176,f177,f6785])).
% 6.85/1.32  fof(f6785,plain,(
% 6.85/1.32    spl4_1 | ~spl4_2 | ~spl4_3),
% 6.85/1.32    inference(avatar_contradiction_clause,[],[f6784])).
% 6.85/1.32  fof(f6784,plain,(
% 6.85/1.32    $false | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 6.85/1.32    inference(subsumption_resolution,[],[f6770,f56])).
% 6.85/1.32  fof(f56,plain,(
% 6.85/1.32    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl4_1),
% 6.85/1.32    inference(avatar_component_clause,[],[f54])).
% 6.85/1.32  fof(f54,plain,(
% 6.85/1.32    spl4_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 6.85/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 6.85/1.32  fof(f6770,plain,(
% 6.85/1.32    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | (~spl4_2 | ~spl4_3)),
% 6.85/1.32    inference(resolution,[],[f6752,f84])).
% 6.85/1.32  fof(f84,plain,(
% 6.85/1.32    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl4_3),
% 6.85/1.32    inference(duplicate_literal_removal,[],[f83])).
% 6.85/1.32  fof(f83,plain,(
% 6.85/1.32    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl4_3),
% 6.85/1.32    inference(superposition,[],[f48,f78])).
% 6.85/1.32  fof(f78,plain,(
% 6.85/1.32    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_3),
% 6.85/1.32    inference(avatar_component_clause,[],[f76])).
% 6.85/1.32  fof(f76,plain,(
% 6.85/1.32    spl4_3 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 6.85/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 6.85/1.32  fof(f48,plain,(
% 6.85/1.32    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 6.85/1.32    inference(equality_resolution,[],[f32])).
% 6.85/1.32  fof(f32,plain,(
% 6.85/1.32    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.85/1.32    inference(cnf_transformation,[],[f2])).
% 6.85/1.32  fof(f2,axiom,(
% 6.85/1.32    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.85/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 6.85/1.32  fof(f6752,plain,(
% 6.85/1.32    ( ! [X0] : (r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0) | k4_xboole_0(k1_tarski(sK0),sK1) = X0) ) | ~spl4_2),
% 6.85/1.32    inference(duplicate_literal_removal,[],[f6718])).
% 6.85/1.32  fof(f6718,plain,(
% 6.85/1.32    ( ! [X0] : (r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0) | k4_xboole_0(k1_tarski(sK0),sK1) = X0 | r2_hidden(sK2(k1_tarski(sK0),sK1,X0),X0) | k4_xboole_0(k1_tarski(sK0),sK1) = X0) ) | ~spl4_2),
% 6.85/1.32    inference(resolution,[],[f6084,f30])).
% 6.85/1.32  fof(f30,plain,(
% 6.85/1.32    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 6.85/1.32    inference(cnf_transformation,[],[f2])).
% 6.85/1.32  fof(f6084,plain,(
% 6.85/1.32    ( ! [X6,X5] : (r2_hidden(sK2(k1_tarski(sK0),X5,X6),sK1) | r2_hidden(sK2(k1_tarski(sK0),X5,X6),X6) | k4_xboole_0(k1_tarski(sK0),X5) = X6) ) | ~spl4_2),
% 6.85/1.32    inference(resolution,[],[f6079,f29])).
% 6.85/1.32  fof(f29,plain,(
% 6.85/1.32    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 6.85/1.32    inference(cnf_transformation,[],[f2])).
% 6.85/1.32  fof(f6079,plain,(
% 6.85/1.32    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,sK1)) ) | ~spl4_2),
% 6.85/1.32    inference(condensation,[],[f6067])).
% 6.85/1.32  fof(f6067,plain,(
% 6.85/1.32    ( ! [X0,X1] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(X0,sK1) | ~r2_hidden(X0,X1)) ) | ~spl4_2),
% 6.85/1.32    inference(resolution,[],[f6060,f47])).
% 6.85/1.32  fof(f47,plain,(
% 6.85/1.32    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 6.85/1.32    inference(equality_resolution,[],[f33])).
% 6.85/1.32  fof(f33,plain,(
% 6.85/1.32    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.85/1.32    inference(cnf_transformation,[],[f2])).
% 6.85/1.32  fof(f6060,plain,(
% 6.85/1.32    ( ! [X6,X5] : (~r2_hidden(X6,k4_xboole_0(X5,sK1)) | ~r2_hidden(X6,k1_tarski(sK0))) ) | ~spl4_2),
% 6.85/1.32    inference(superposition,[],[f48,f6047])).
% 6.85/1.32  fof(f6047,plain,(
% 6.85/1.32    ( ! [X13] : (k4_xboole_0(X13,sK1) = k4_xboole_0(k4_xboole_0(X13,sK1),k1_tarski(sK0))) ) | ~spl4_2),
% 6.85/1.32    inference(resolution,[],[f89,f59])).
% 6.85/1.32  fof(f59,plain,(
% 6.85/1.32    r2_hidden(sK0,sK1) | ~spl4_2),
% 6.85/1.32    inference(avatar_component_clause,[],[f58])).
% 6.85/1.32  fof(f58,plain,(
% 6.85/1.32    spl4_2 <=> r2_hidden(sK0,sK1)),
% 6.85/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 6.85/1.32  fof(f89,plain,(
% 6.85/1.32    ( ! [X4,X5,X3] : (~r2_hidden(X5,X4) | k4_xboole_0(X3,X4) = k4_xboole_0(k4_xboole_0(X3,X4),k1_tarski(X5))) )),
% 6.85/1.32    inference(resolution,[],[f34,f48])).
% 6.85/1.32  fof(f34,plain,(
% 6.85/1.32    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 6.85/1.32    inference(cnf_transformation,[],[f22])).
% 6.85/1.32  fof(f22,axiom,(
% 6.85/1.32    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 6.85/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 6.85/1.32  fof(f177,plain,(
% 6.85/1.32    ~spl4_2 | ~spl4_4),
% 6.85/1.32    inference(avatar_split_clause,[],[f101,f94,f58])).
% 6.85/1.32  fof(f94,plain,(
% 6.85/1.32    spl4_4 <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 6.85/1.32    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 6.85/1.32  fof(f101,plain,(
% 6.85/1.32    ~r2_hidden(sK0,sK1) | ~spl4_4),
% 6.85/1.32    inference(trivial_inequality_removal,[],[f98])).
% 6.85/1.32  fof(f98,plain,(
% 6.85/1.32    sK1 != sK1 | ~r2_hidden(sK0,sK1) | ~spl4_4),
% 6.85/1.32    inference(superposition,[],[f35,f96])).
% 6.85/1.32  fof(f96,plain,(
% 6.85/1.32    sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) | ~spl4_4),
% 6.85/1.32    inference(avatar_component_clause,[],[f94])).
% 6.85/1.32  fof(f35,plain,(
% 6.85/1.32    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 6.85/1.32    inference(cnf_transformation,[],[f22])).
% 6.85/1.32  fof(f176,plain,(
% 6.85/1.32    ~spl4_2 | ~spl4_4),
% 6.85/1.32    inference(avatar_split_clause,[],[f102,f94,f58])).
% 6.85/1.32  fof(f102,plain,(
% 6.85/1.32    ~r2_hidden(sK0,sK1) | ~spl4_4),
% 6.85/1.32    inference(resolution,[],[f100,f52])).
% 6.85/1.32  fof(f52,plain,(
% 6.85/1.32    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 6.85/1.32    inference(equality_resolution,[],[f51])).
% 6.85/1.32  fof(f51,plain,(
% 6.85/1.32    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 6.85/1.32    inference(equality_resolution,[],[f36])).
% 6.85/1.32  fof(f36,plain,(
% 6.85/1.32    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 6.85/1.32    inference(cnf_transformation,[],[f12])).
% 6.85/1.32  fof(f12,axiom,(
% 6.85/1.32    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.85/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 6.85/1.32  fof(f100,plain,(
% 6.85/1.32    ( ! [X1] : (~r2_hidden(X1,k1_tarski(sK0)) | ~r2_hidden(X1,sK1)) ) | ~spl4_4),
% 6.85/1.32    inference(superposition,[],[f48,f96])).
% 6.85/1.32  fof(f175,plain,(
% 6.85/1.32    ~spl4_1 | ~spl4_3 | ~spl4_4),
% 6.85/1.32    inference(avatar_contradiction_clause,[],[f173])).
% 6.85/1.32  fof(f173,plain,(
% 6.85/1.32    $false | (~spl4_1 | ~spl4_3 | ~spl4_4)),
% 6.85/1.32    inference(resolution,[],[f172,f52])).
% 6.85/1.32  fof(f172,plain,(
% 6.85/1.32    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0))) ) | (~spl4_1 | ~spl4_3 | ~spl4_4)),
% 6.85/1.32    inference(subsumption_resolution,[],[f171,f100])).
% 6.85/1.32  fof(f171,plain,(
% 6.85/1.32    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_tarski(sK0))) ) | (~spl4_1 | ~spl4_3)),
% 6.85/1.32    inference(subsumption_resolution,[],[f160,f84])).
% 6.85/1.32  fof(f160,plain,(
% 6.85/1.32    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_tarski(sK0))) ) | ~spl4_1),
% 6.85/1.32    inference(superposition,[],[f47,f55])).
% 6.85/1.32  fof(f55,plain,(
% 6.85/1.32    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl4_1),
% 6.85/1.32    inference(avatar_component_clause,[],[f54])).
% 6.85/1.32  fof(f97,plain,(
% 6.85/1.32    spl4_4 | spl4_2),
% 6.85/1.32    inference(avatar_split_clause,[],[f87,f58,f94])).
% 6.85/1.32  fof(f87,plain,(
% 6.85/1.32    sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) | spl4_2),
% 6.85/1.32    inference(resolution,[],[f34,f60])).
% 6.85/1.32  fof(f60,plain,(
% 6.85/1.32    ~r2_hidden(sK0,sK1) | spl4_2),
% 6.85/1.32    inference(avatar_component_clause,[],[f58])).
% 6.85/1.32  fof(f80,plain,(
% 6.85/1.32    spl4_3),
% 6.85/1.32    inference(avatar_split_clause,[],[f74,f76])).
% 6.85/1.32  fof(f74,plain,(
% 6.85/1.32    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 6.85/1.32    inference(superposition,[],[f46,f65])).
% 6.85/1.32  fof(f65,plain,(
% 6.85/1.32    ( ! [X6] : (k5_xboole_0(k1_xboole_0,X6) = X6) )),
% 6.85/1.32    inference(superposition,[],[f45,f41])).
% 6.85/1.32  fof(f41,plain,(
% 6.85/1.32    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.85/1.32    inference(cnf_transformation,[],[f6])).
% 6.85/1.32  fof(f6,axiom,(
% 6.85/1.32    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 6.85/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 6.85/1.32  fof(f45,plain,(
% 6.85/1.32    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 6.85/1.32    inference(cnf_transformation,[],[f1])).
% 6.85/1.32  fof(f1,axiom,(
% 6.85/1.32    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 6.85/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 6.85/1.32  fof(f46,plain,(
% 6.85/1.32    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 6.85/1.32    inference(definition_unfolding,[],[f42,f40])).
% 6.85/1.32  fof(f40,plain,(
% 6.85/1.32    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.85/1.32    inference(cnf_transformation,[],[f11])).
% 6.85/1.32  fof(f11,axiom,(
% 6.85/1.32    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.85/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 6.85/1.32  fof(f42,plain,(
% 6.85/1.32    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.85/1.32    inference(cnf_transformation,[],[f5])).
% 6.85/1.32  fof(f5,axiom,(
% 6.85/1.32    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.85/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 6.85/1.32  fof(f79,plain,(
% 6.85/1.32    spl4_3),
% 6.85/1.32    inference(avatar_split_clause,[],[f71,f76])).
% 6.85/1.32  fof(f71,plain,(
% 6.85/1.32    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 6.85/1.32    inference(superposition,[],[f65,f46])).
% 6.85/1.32  fof(f62,plain,(
% 6.85/1.32    spl4_1 | spl4_2),
% 6.85/1.32    inference(avatar_split_clause,[],[f26,f58,f54])).
% 6.85/1.32  fof(f26,plain,(
% 6.85/1.32    r2_hidden(sK0,sK1) | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 6.85/1.32    inference(cnf_transformation,[],[f25])).
% 6.85/1.32  fof(f25,plain,(
% 6.85/1.32    ? [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 6.85/1.32    inference(ennf_transformation,[],[f24])).
% 6.85/1.32  fof(f24,negated_conjecture,(
% 6.85/1.32    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.85/1.32    inference(negated_conjecture,[],[f23])).
% 6.85/1.32  fof(f23,conjecture,(
% 6.85/1.32    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 6.85/1.32    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 6.85/1.32  fof(f61,plain,(
% 6.85/1.32    ~spl4_1 | ~spl4_2),
% 6.85/1.32    inference(avatar_split_clause,[],[f27,f58,f54])).
% 6.85/1.32  fof(f27,plain,(
% 6.85/1.32    ~r2_hidden(sK0,sK1) | k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 6.85/1.32    inference(cnf_transformation,[],[f25])).
% 6.85/1.32  % SZS output end Proof for theBenchmark
% 6.85/1.32  % (1353)------------------------------
% 6.85/1.32  % (1353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.85/1.32  % (1353)Termination reason: Refutation
% 6.85/1.32  
% 6.85/1.32  % (1353)Memory used [KB]: 7931
% 6.85/1.32  % (1353)Time elapsed: 0.899 s
% 6.85/1.32  % (1353)------------------------------
% 6.85/1.32  % (1353)------------------------------
% 6.85/1.32  % (1352)Success in time 0.948 s
%------------------------------------------------------------------------------
