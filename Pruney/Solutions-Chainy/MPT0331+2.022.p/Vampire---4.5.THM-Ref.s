%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  69 expanded)
%              Number of leaves         :   14 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 ( 177 expanded)
%              Number of equality atoms :   57 (  75 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f80,f97,f98,f99])).

fof(f99,plain,
    ( sK1 != sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)
    | r2_hidden(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f98,plain,
    ( sK0 != sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)
    | r2_hidden(sK0,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f97,plain,
    ( spl5_5
    | spl5_6
    | ~ spl5_4
    | spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f87,f77,f67,f77,f94,f90])).

fof(f90,plain,
    ( spl5_5
  <=> sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f94,plain,
    ( spl5_6
  <=> sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f67,plain,
    ( spl5_3
  <=> sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f77,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f87,plain,
    ( ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)
    | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl5_3
    | ~ spl5_4 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)
    | sK2 != sK2
    | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2)
    | spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f83,f79])).

fof(f79,plain,
    ( r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f83,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),sK2)
        | ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),X1)
        | sK2 != X1
        | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1)
        | sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1) )
    | spl5_3 ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ! [X1] :
        ( sK2 != X1
        | ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),X1)
        | ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),sK2)
        | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1)
        | sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1)
        | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1) )
    | spl5_3 ),
    inference(resolution,[],[f71,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f26,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f71,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X0),k2_enumset1(sK0,sK0,sK0,sK1))
        | sK2 != X0
        | ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X0),X0)
        | ~ r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X0),sK2) )
    | spl5_3 ),
    inference(superposition,[],[f69,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f16,f14])).

fof(f14,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f69,plain,
    ( sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f80,plain,
    ( spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f75,f67,f77])).

fof(f75,plain,
    ( r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)
    | spl5_3 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)
    | sK2 != sK2
    | spl5_3 ),
    inference(factoring,[],[f72])).

fof(f72,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),sK2)
        | r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),X1)
        | sK2 != X1 )
    | spl5_3 ),
    inference(superposition,[],[f69,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f17,f14])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f70,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f12,f14,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f13,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

% (24633)Refutation not found, incomplete strategy% (24633)------------------------------
% (24633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f12,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f65,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f11,f62])).

fof(f62,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f11,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f10,f57])).

fof(f57,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f10,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (24621)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (24623)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.50  % (24637)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.50  % (24639)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.51  % (24615)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.51  % (24616)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (24631)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.51  % (24630)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.51  % (24629)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (24622)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.52  % (24614)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (24612)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (24614)Refutation not found, incomplete strategy% (24614)------------------------------
% 0.19/0.52  % (24614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (24614)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (24614)Memory used [KB]: 10618
% 0.19/0.52  % (24614)Time elapsed: 0.126 s
% 0.19/0.52  % (24614)------------------------------
% 0.19/0.52  % (24614)------------------------------
% 0.19/0.52  % (24638)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.52  % (24629)Refutation not found, incomplete strategy% (24629)------------------------------
% 0.19/0.52  % (24629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (24629)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (24629)Memory used [KB]: 10618
% 0.19/0.52  % (24629)Time elapsed: 0.117 s
% 0.19/0.52  % (24629)------------------------------
% 0.19/0.52  % (24629)------------------------------
% 0.19/0.53  % (24636)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.53  % (24625)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.53  % (24640)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.53  % (24613)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (24641)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (24634)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (24635)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.53  % (24617)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (24626)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.54  % (24633)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.54  % (24627)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.54  % (24618)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.54  % (24632)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.54  % (24619)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.54  % (24628)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.54  % (24634)Refutation found. Thanks to Tanya!
% 0.19/0.54  % SZS status Theorem for theBenchmark
% 0.19/0.54  % (24632)Refutation not found, incomplete strategy% (24632)------------------------------
% 0.19/0.54  % (24632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (24620)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.54  % (24624)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f100,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(avatar_sat_refutation,[],[f60,f65,f70,f80,f97,f98,f99])).
% 0.19/0.54  fof(f99,plain,(
% 0.19/0.54    sK1 != sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) | r2_hidden(sK1,sK2)),
% 0.19/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.54  fof(f98,plain,(
% 0.19/0.54    sK0 != sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2) | ~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) | r2_hidden(sK0,sK2)),
% 0.19/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.54  fof(f97,plain,(
% 0.19/0.54    spl5_5 | spl5_6 | ~spl5_4 | spl5_3 | ~spl5_4),
% 0.19/0.54    inference(avatar_split_clause,[],[f87,f77,f67,f77,f94,f90])).
% 0.19/0.54  fof(f90,plain,(
% 0.19/0.54    spl5_5 <=> sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.54  fof(f94,plain,(
% 0.19/0.54    spl5_6 <=> sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.54  fof(f67,plain,(
% 0.19/0.54    spl5_3 <=> sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.54  fof(f77,plain,(
% 0.19/0.54    spl5_4 <=> r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.54  fof(f87,plain,(
% 0.19/0.54    ~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2) | sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2) | (spl5_3 | ~spl5_4)),
% 0.19/0.54    inference(trivial_inequality_removal,[],[f86])).
% 0.19/0.54  fof(f86,plain,(
% 0.19/0.54    ~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) | sK2 != sK2 | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2) | sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2) | (spl5_3 | ~spl5_4)),
% 0.19/0.54    inference(resolution,[],[f83,f79])).
% 0.19/0.54  fof(f79,plain,(
% 0.19/0.54    r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) | ~spl5_4),
% 0.19/0.54    inference(avatar_component_clause,[],[f77])).
% 0.19/0.54  fof(f83,plain,(
% 0.19/0.54    ( ! [X1] : (~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),sK2) | ~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),X1) | sK2 != X1 | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1) | sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1)) ) | spl5_3),
% 0.19/0.54    inference(duplicate_literal_removal,[],[f82])).
% 0.19/0.54  fof(f82,plain,(
% 0.19/0.54    ( ! [X1] : (sK2 != X1 | ~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),X1) | ~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),sK2) | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1) | sK1 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1) | sK0 = sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1)) ) | spl5_3),
% 0.19/0.54    inference(resolution,[],[f71,f55])).
% 0.19/0.54  fof(f55,plain,(
% 0.19/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.19/0.54    inference(equality_resolution,[],[f41])).
% 0.19/0.54  fof(f41,plain,(
% 0.19/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.19/0.54    inference(definition_unfolding,[],[f26,f15])).
% 0.19/0.54  fof(f15,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.19/0.54    inference(cnf_transformation,[],[f9])).
% 0.19/0.54  fof(f9,plain,(
% 0.19/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.19/0.54    inference(ennf_transformation,[],[f3])).
% 0.19/0.54  fof(f3,axiom,(
% 0.19/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.19/0.54  fof(f71,plain,(
% 0.19/0.54    ( ! [X0] : (r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X0),k2_enumset1(sK0,sK0,sK0,sK1)) | sK2 != X0 | ~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X0),X0) | ~r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X0),sK2)) ) | spl5_3),
% 0.19/0.54    inference(superposition,[],[f69,f37])).
% 0.19/0.54  fof(f37,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f16,f14])).
% 0.19/0.54  fof(f14,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.54    inference(cnf_transformation,[],[f2])).
% 0.19/0.54  fof(f2,axiom,(
% 0.19/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.54  fof(f16,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.19/0.54    inference(cnf_transformation,[],[f1])).
% 0.19/0.54  fof(f1,axiom,(
% 0.19/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.19/0.54  fof(f69,plain,(
% 0.19/0.54    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))) | spl5_3),
% 0.19/0.54    inference(avatar_component_clause,[],[f67])).
% 0.19/0.54  fof(f80,plain,(
% 0.19/0.54    spl5_4 | spl5_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f75,f67,f77])).
% 0.19/0.54  fof(f75,plain,(
% 0.19/0.54    r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) | spl5_3),
% 0.19/0.54    inference(trivial_inequality_removal,[],[f74])).
% 0.19/0.54  fof(f74,plain,(
% 0.19/0.54    r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),sK2),sK2) | sK2 != sK2 | spl5_3),
% 0.19/0.54    inference(factoring,[],[f72])).
% 0.19/0.54  fof(f72,plain,(
% 0.19/0.54    ( ! [X1] : (r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),sK2) | r2_hidden(sK3(sK2,k2_enumset1(sK0,sK0,sK0,sK1),X1),X1) | sK2 != X1) ) | spl5_3),
% 0.19/0.54    inference(superposition,[],[f69,f36])).
% 0.19/0.54  fof(f36,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f17,f14])).
% 0.19/0.54  fof(f17,plain,(
% 0.19/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.19/0.54    inference(cnf_transformation,[],[f1])).
% 0.19/0.54  fof(f70,plain,(
% 0.19/0.54    ~spl5_3),
% 0.19/0.54    inference(avatar_split_clause,[],[f31,f67])).
% 0.19/0.54  fof(f31,plain,(
% 0.19/0.54    sK2 != k5_xboole_0(sK2,k3_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.19/0.54    inference(definition_unfolding,[],[f12,f14,f30])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.54    inference(definition_unfolding,[],[f13,f15])).
% 0.19/0.54  fof(f13,plain,(
% 0.19/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f4])).
% 0.19/0.54  fof(f4,axiom,(
% 0.19/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.54  % (24633)Refutation not found, incomplete strategy% (24633)------------------------------
% 0.19/0.54  % (24633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  fof(f12,plain,(
% 0.19/0.54    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 0.19/0.54    inference(cnf_transformation,[],[f8])).
% 0.19/0.54  fof(f8,plain,(
% 0.19/0.54    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.19/0.54    inference(ennf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,negated_conjecture,(
% 0.19/0.54    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.19/0.54    inference(negated_conjecture,[],[f6])).
% 0.19/0.54  fof(f6,conjecture,(
% 0.19/0.54    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.19/0.54  fof(f65,plain,(
% 0.19/0.54    ~spl5_2),
% 0.19/0.54    inference(avatar_split_clause,[],[f11,f62])).
% 0.19/0.54  fof(f62,plain,(
% 0.19/0.54    spl5_2 <=> r2_hidden(sK1,sK2)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.54  fof(f11,plain,(
% 0.19/0.54    ~r2_hidden(sK1,sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f8])).
% 0.19/0.54  fof(f60,plain,(
% 0.19/0.54    ~spl5_1),
% 0.19/0.54    inference(avatar_split_clause,[],[f10,f57])).
% 0.19/0.54  fof(f57,plain,(
% 0.19/0.54    spl5_1 <=> r2_hidden(sK0,sK2)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.54  fof(f10,plain,(
% 0.19/0.54    ~r2_hidden(sK0,sK2)),
% 0.19/0.54    inference(cnf_transformation,[],[f8])).
% 0.19/0.54  % SZS output end Proof for theBenchmark
% 0.19/0.54  % (24634)------------------------------
% 0.19/0.54  % (24634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (24634)Termination reason: Refutation
% 0.19/0.54  
% 0.19/0.54  % (24634)Memory used [KB]: 10746
% 0.19/0.54  % (24634)Time elapsed: 0.142 s
% 0.19/0.54  % (24634)------------------------------
% 0.19/0.54  % (24634)------------------------------
% 0.19/0.55  % (24611)Success in time 0.19 s
%------------------------------------------------------------------------------
