%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:28 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 105 expanded)
%              Number of leaves         :   15 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 ( 313 expanded)
%              Number of equality atoms :   67 ( 163 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f78,f98,f128,f250,f255])).

fof(f255,plain,
    ( spl3_4
    | spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl3_4
    | spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f93,f64,f96,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f96,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_7
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

% (12610)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f64,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_4
  <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f93,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_6
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f250,plain,
    ( spl3_3
    | ~ spl3_6
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl3_3
    | ~ spl3_6
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f97,f92,f59,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X1,X0),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f42,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f59,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK1,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_3
  <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f92,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f97,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f128,plain,
    ( spl3_6
    | spl3_7
    | spl3_2 ),
    inference(avatar_split_clause,[],[f126,f52,f95,f91])).

fof(f52,plain,
    ( spl3_2
  <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f126,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f119])).

fof(f119,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | spl3_2 ),
    inference(superposition,[],[f54,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f54,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f98,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f83,f75,f95,f91])).

fof(f75,plain,
    ( spl3_5
  <=> r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f83,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | spl3_5 ),
    inference(resolution,[],[f38,f77])).

fof(f77,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f78,plain,
    ( ~ spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f71,f47,f75])).

fof(f47,plain,
    ( spl3_1
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f71,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2)
    | spl3_1 ),
    inference(superposition,[],[f49,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f49,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f65,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f40,f62])).

fof(f40,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f22,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
    & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
    & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) )
   => ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)
      & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
      & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
          & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)
        & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).

fof(f60,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f39,f57])).

fof(f39,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f23,plain,(
    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (12615)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (12614)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (12613)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (12599)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (12606)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.44/0.55  % (12605)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.44/0.55  % (12597)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.55  % (12607)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.55  % (12598)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.56  % (12607)Refutation not found, incomplete strategy% (12607)------------------------------
% 1.44/0.56  % (12607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (12615)Refutation not found, incomplete strategy% (12615)------------------------------
% 1.44/0.56  % (12615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (12607)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (12607)Memory used [KB]: 10618
% 1.44/0.56  % (12607)Time elapsed: 0.130 s
% 1.44/0.56  % (12607)------------------------------
% 1.44/0.56  % (12607)------------------------------
% 1.53/0.56  % (12615)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (12615)Memory used [KB]: 10618
% 1.53/0.56  % (12615)Time elapsed: 0.129 s
% 1.53/0.56  % (12615)------------------------------
% 1.53/0.56  % (12615)------------------------------
% 1.53/0.57  % (12605)Refutation not found, incomplete strategy% (12605)------------------------------
% 1.53/0.57  % (12605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (12605)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (12605)Memory used [KB]: 1663
% 1.53/0.57  % (12605)Time elapsed: 0.132 s
% 1.53/0.57  % (12605)------------------------------
% 1.53/0.57  % (12605)------------------------------
% 1.53/0.57  % (12614)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f256,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(avatar_sat_refutation,[],[f50,f55,f60,f65,f78,f98,f128,f250,f255])).
% 1.53/0.57  fof(f255,plain,(
% 1.53/0.57    spl3_4 | spl3_6 | ~spl3_7),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f254])).
% 1.53/0.57  fof(f254,plain,(
% 1.53/0.57    $false | (spl3_4 | spl3_6 | ~spl3_7)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f93,f64,f96,f42])).
% 1.53/0.57  fof(f42,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.53/0.57    inference(definition_unfolding,[],[f27,f29])).
% 1.53/0.57  fof(f29,plain,(
% 1.53/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.57  fof(f27,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.53/0.57    inference(flattening,[],[f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.53/0.57    inference(nnf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.53/0.57  fof(f96,plain,(
% 1.53/0.57    r2_hidden(sK1,sK2) | ~spl3_7),
% 1.53/0.57    inference(avatar_component_clause,[],[f95])).
% 1.53/0.57  fof(f95,plain,(
% 1.53/0.57    spl3_7 <=> r2_hidden(sK1,sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.53/0.57  % (12610)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.53/0.57  fof(f64,plain,(
% 1.53/0.57    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0) | spl3_4),
% 1.53/0.57    inference(avatar_component_clause,[],[f62])).
% 1.53/0.57  fof(f62,plain,(
% 1.53/0.57    spl3_4 <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK0,sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.53/0.57  fof(f93,plain,(
% 1.53/0.57    ~r2_hidden(sK0,sK2) | spl3_6),
% 1.53/0.57    inference(avatar_component_clause,[],[f91])).
% 1.53/0.57  fof(f91,plain,(
% 1.53/0.57    spl3_6 <=> r2_hidden(sK0,sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.53/0.57  fof(f250,plain,(
% 1.53/0.57    spl3_3 | ~spl3_6 | spl3_7),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f195])).
% 1.53/0.57  fof(f195,plain,(
% 1.53/0.57    $false | (spl3_3 | ~spl3_6 | spl3_7)),
% 1.53/0.57    inference(unit_resulting_resolution,[],[f97,f92,f59,f130])).
% 1.53/0.57  fof(f130,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X1,X0),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.53/0.57    inference(superposition,[],[f42,f33])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.53/0.57  fof(f59,plain,(
% 1.53/0.57    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK1,sK1) | spl3_3),
% 1.53/0.57    inference(avatar_component_clause,[],[f57])).
% 1.53/0.57  fof(f57,plain,(
% 1.53/0.57    spl3_3 <=> k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k2_tarski(sK1,sK1)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.53/0.57  fof(f92,plain,(
% 1.53/0.57    r2_hidden(sK0,sK2) | ~spl3_6),
% 1.53/0.57    inference(avatar_component_clause,[],[f91])).
% 1.53/0.57  fof(f97,plain,(
% 1.53/0.57    ~r2_hidden(sK1,sK2) | spl3_7),
% 1.53/0.57    inference(avatar_component_clause,[],[f95])).
% 1.53/0.57  fof(f128,plain,(
% 1.53/0.57    spl3_6 | spl3_7 | spl3_2),
% 1.53/0.57    inference(avatar_split_clause,[],[f126,f52,f95,f91])).
% 1.53/0.57  fof(f52,plain,(
% 1.53/0.57    spl3_2 <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.53/0.57  fof(f126,plain,(
% 1.53/0.57    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | spl3_2),
% 1.53/0.57    inference(trivial_inequality_removal,[],[f119])).
% 1.53/0.57  fof(f119,plain,(
% 1.53/0.57    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | spl3_2),
% 1.53/0.57    inference(superposition,[],[f54,f32])).
% 1.53/0.57  fof(f32,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f17])).
% 1.53/0.57  fof(f17,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.53/0.57    inference(flattening,[],[f16])).
% 1.53/0.57  fof(f16,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.53/0.57    inference(nnf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 1.53/0.57  fof(f54,plain,(
% 1.53/0.57    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | spl3_2),
% 1.53/0.57    inference(avatar_component_clause,[],[f52])).
% 1.53/0.57  fof(f98,plain,(
% 1.53/0.57    ~spl3_6 | ~spl3_7 | spl3_5),
% 1.53/0.57    inference(avatar_split_clause,[],[f83,f75,f95,f91])).
% 1.53/0.57  fof(f75,plain,(
% 1.53/0.57    spl3_5 <=> r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.53/0.57  fof(f83,plain,(
% 1.53/0.57    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | spl3_5),
% 1.53/0.57    inference(resolution,[],[f38,f77])).
% 1.53/0.57  fof(f77,plain,(
% 1.53/0.57    ~r1_tarski(k2_tarski(sK0,sK1),sK2) | spl3_5),
% 1.53/0.57    inference(avatar_component_clause,[],[f75])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f20])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.53/0.57    inference(flattening,[],[f19])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.53/0.57    inference(nnf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.53/0.57  fof(f78,plain,(
% 1.53/0.57    ~spl3_5 | spl3_1),
% 1.53/0.57    inference(avatar_split_clause,[],[f71,f47,f75])).
% 1.53/0.57  fof(f47,plain,(
% 1.53/0.57    spl3_1 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.53/0.57  fof(f71,plain,(
% 1.53/0.57    ~r1_tarski(k2_tarski(sK0,sK1),sK2) | spl3_1),
% 1.53/0.57    inference(trivial_inequality_removal,[],[f69])).
% 1.53/0.57  fof(f69,plain,(
% 1.53/0.57    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_tarski(sK0,sK1),sK2) | spl3_1),
% 1.53/0.57    inference(superposition,[],[f49,f35])).
% 1.53/0.57  fof(f35,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f18])).
% 1.53/0.57  fof(f18,plain,(
% 1.53/0.57    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.53/0.57    inference(nnf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.53/0.57  fof(f49,plain,(
% 1.53/0.57    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | spl3_1),
% 1.53/0.57    inference(avatar_component_clause,[],[f47])).
% 1.53/0.57  fof(f65,plain,(
% 1.53/0.57    ~spl3_4),
% 1.53/0.57    inference(avatar_split_clause,[],[f40,f62])).
% 1.53/0.57  fof(f40,plain,(
% 1.53/0.57    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK0,sK0)),
% 1.53/0.57    inference(definition_unfolding,[],[f22,f29])).
% 1.53/0.57  fof(f22,plain,(
% 1.53/0.57    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0)),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,plain,(
% 1.53/0.57    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.53/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 1.53/0.57  fof(f12,plain,(
% 1.53/0.57    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2)) => (k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1) & k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK0) & k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.53/0.57    introduced(choice_axiom,[])).
% 1.53/0.57  fof(f11,plain,(
% 1.53/0.57    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 1.53/0.57    inference(ennf_transformation,[],[f10])).
% 1.53/0.57  fof(f10,negated_conjecture,(
% 1.53/0.57    ~! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 1.53/0.57    inference(negated_conjecture,[],[f9])).
% 1.53/0.57  fof(f9,conjecture,(
% 1.53/0.57    ! [X0,X1,X2] : ~(k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) & k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X1),X2))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_zfmisc_1)).
% 1.53/0.57  fof(f60,plain,(
% 1.53/0.57    ~spl3_3),
% 1.53/0.57    inference(avatar_split_clause,[],[f39,f57])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k2_tarski(sK1,sK1)),
% 1.53/0.57    inference(definition_unfolding,[],[f23,f29])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    k4_xboole_0(k2_tarski(sK0,sK1),sK2) != k1_tarski(sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f55,plain,(
% 1.53/0.57    ~spl3_2),
% 1.53/0.57    inference(avatar_split_clause,[],[f24,f52])).
% 1.53/0.57  fof(f24,plain,(
% 1.53/0.57    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f50,plain,(
% 1.53/0.57    ~spl3_1),
% 1.53/0.57    inference(avatar_split_clause,[],[f21,f47])).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (12614)------------------------------
% 1.53/0.57  % (12614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (12614)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (12614)Memory used [KB]: 10874
% 1.53/0.57  % (12614)Time elapsed: 0.136 s
% 1.53/0.57  % (12614)------------------------------
% 1.53/0.57  % (12614)------------------------------
% 1.53/0.57  % (12604)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.53/0.57  % (12600)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.53/0.57  % (12616)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.53/0.57  % (12608)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.53/0.57  % (12618)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.53/0.57  % (12612)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.53/0.57  % (12618)Refutation not found, incomplete strategy% (12618)------------------------------
% 1.53/0.57  % (12618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (12618)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (12618)Memory used [KB]: 6140
% 1.53/0.57  % (12618)Time elapsed: 0.150 s
% 1.53/0.57  % (12618)------------------------------
% 1.53/0.57  % (12618)------------------------------
% 1.53/0.58  % (12608)Refutation not found, incomplete strategy% (12608)------------------------------
% 1.53/0.58  % (12608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (12592)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.53/0.58  % (12596)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.53/0.58  % (12608)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (12608)Memory used [KB]: 1663
% 1.53/0.58  % (12608)Time elapsed: 0.104 s
% 1.53/0.58  % (12608)------------------------------
% 1.53/0.58  % (12608)------------------------------
% 1.53/0.58  % (12602)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.58  % (12592)Refutation not found, incomplete strategy% (12592)------------------------------
% 1.53/0.58  % (12592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (12592)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (12592)Memory used [KB]: 1663
% 1.53/0.58  % (12592)Time elapsed: 0.117 s
% 1.53/0.58  % (12592)------------------------------
% 1.53/0.58  % (12592)------------------------------
% 1.53/0.58  % (12593)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.53/0.58  % (12590)Success in time 0.214 s
%------------------------------------------------------------------------------
