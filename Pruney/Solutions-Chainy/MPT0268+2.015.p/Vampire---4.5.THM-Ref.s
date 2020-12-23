%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  98 expanded)
%              Number of leaves         :   12 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 224 expanded)
%              Number of equality atoms :   65 ( 105 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f104,f111,f124,f138,f152])).

fof(f152,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f92,f83,f134])).

fof(f134,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1))
        | ~ r2_hidden(X4,sK0) )
    | ~ spl6_1 ),
    inference(superposition,[],[f73,f87])).

fof(f87,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl6_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f83,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k2_enumset1(X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f92,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f138,plain,
    ( sK1 != sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f124,plain,
    ( spl6_5
    | ~ spl6_4
    | spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f118,f108,f86,f108,f121])).

fof(f121,plain,
    ( spl6_5
  <=> sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f108,plain,
    ( spl6_4
  <=> r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f118,plain,
    ( ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl6_1
    | ~ spl6_4 ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | sK0 != sK0
    | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl6_1
    | ~ spl6_4 ),
    inference(resolution,[],[f114,f110])).

fof(f110,plain,
    ( r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f114,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0)
        | ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1)
        | sK0 != X1
        | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1) )
    | spl6_1 ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( ! [X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1)
        | ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0)
        | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1)
        | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1)
        | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1) )
    | spl6_1 ),
    inference(resolution,[],[f94,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k2_enumset1(X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f47,f30])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),k2_enumset1(sK1,sK1,sK1,sK1))
        | sK0 != X0
        | ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),X0)
        | ~ r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),sK0) )
    | spl6_1 ),
    inference(superposition,[],[f88,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f88,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f111,plain,
    ( spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f106,f86,f108])).

fof(f106,plain,
    ( r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)
    | sK0 != sK0
    | spl6_1 ),
    inference(factoring,[],[f95])).

fof(f95,plain,
    ( ! [X1] :
        ( r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0)
        | r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1)
        | sK0 != X1 )
    | spl6_1 ),
    inference(superposition,[],[f88,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f104,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f54,f90,f86])).

fof(f54,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f19,f26,f52])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f93,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f53,f90,f86])).

fof(f53,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f20,f26,f52])).

fof(f20,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:19:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (18413)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (18418)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (18414)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (18429)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.51  % (18430)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (18414)Refutation not found, incomplete strategy% (18414)------------------------------
% 0.21/0.51  % (18414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (18424)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (18414)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (18414)Memory used [KB]: 10746
% 0.21/0.51  % (18414)Time elapsed: 0.106 s
% 0.21/0.51  % (18414)------------------------------
% 0.21/0.51  % (18414)------------------------------
% 0.21/0.51  % (18437)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (18421)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (18425)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (18422)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (18419)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (18411)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (18429)Refutation not found, incomplete strategy% (18429)------------------------------
% 0.21/0.52  % (18429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18426)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (18429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18429)Memory used [KB]: 10618
% 0.21/0.52  % (18429)Time elapsed: 0.111 s
% 0.21/0.52  % (18429)------------------------------
% 0.21/0.52  % (18429)------------------------------
% 0.21/0.53  % (18436)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (18434)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (18415)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (18434)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f93,f104,f111,f124,f138,f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ~spl6_1 | ~spl6_2),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    $false | (~spl6_1 | ~spl6_2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f92,f83,f134])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,k2_enumset1(sK1,sK1,sK1,sK1)) | ~r2_hidden(X4,sK0)) ) | ~spl6_1),
% 0.21/0.53    inference(superposition,[],[f73,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl6_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl6_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f35,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X4,X2,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X1,X2))) )),
% 0.21/0.53    inference(equality_resolution,[],[f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k2_enumset1(X4,X4,X1,X2) != X3) )),
% 0.21/0.53    inference(equality_resolution,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | ~spl6_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl6_2 <=> r2_hidden(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    sK1 != sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | r2_hidden(sK1,sK0)),
% 0.21/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl6_5 | ~spl6_4 | spl6_1 | ~spl6_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f118,f108,f86,f108,f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    spl6_5 <=> sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    spl6_4 <=> r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0) | (spl6_1 | ~spl6_4)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | sK0 != sK0 | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0) | (spl6_1 | ~spl6_4)),
% 0.21/0.53    inference(resolution,[],[f114,f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | ~spl6_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f108])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X1] : (~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0) | ~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1) | sK0 != X1 | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1)) ) | spl6_1),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X1] : (sK0 != X1 | ~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1) | ~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0) | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1) | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1) | sK1 = sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1)) ) | spl6_1),
% 0.21/0.53    inference(resolution,[],[f94,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k2_enumset1(X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.53    inference(equality_resolution,[],[f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.53    inference(definition_unfolding,[],[f47,f30])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),k2_enumset1(sK1,sK1,sK1,sK1)) | sK0 != X0 | ~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),X0) | ~r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X0),sK0)) ) | spl6_1),
% 0.21/0.53    inference(superposition,[],[f88,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f31,f26])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | spl6_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl6_4 | spl6_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f106,f86,f108])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | spl6_1),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),sK0),sK0) | sK0 != sK0 | spl6_1),
% 0.21/0.53    inference(factoring,[],[f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),sK0) | r2_hidden(sK3(sK0,k2_enumset1(sK1,sK1,sK1,sK1),X1),X1) | sK0 != X1) ) | spl6_1),
% 0.21/0.53    inference(superposition,[],[f88,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f26])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl6_1 | ~spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f54,f90,f86])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f19,f26,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f22,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f30])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ~spl6_1 | spl6_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f53,f90,f86])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.21/0.53    inference(definition_unfolding,[],[f20,f26,f52])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (18434)------------------------------
% 0.21/0.53  % (18434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18434)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (18434)Memory used [KB]: 10746
% 0.21/0.53  % (18434)Time elapsed: 0.121 s
% 0.21/0.53  % (18434)------------------------------
% 0.21/0.53  % (18434)------------------------------
% 0.21/0.53  % (18435)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (18408)Success in time 0.168 s
%------------------------------------------------------------------------------
