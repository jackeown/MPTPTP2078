%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:36 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  74 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :  119 ( 165 expanded)
%              Number of equality atoms :   48 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f103,f110,f120,f136,f140])).

fof(f140,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl6_5 ),
    inference(unit_resulting_resolution,[],[f80,f135])).

fof(f135,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_5
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f80,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k1_enumset1(X4,X1,X2)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k1_enumset1(X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f48])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f136,plain,
    ( ~ spl6_5
    | spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f123,f117,f100,f133])).

fof(f100,plain,
    ( spl6_3
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f117,plain,
    ( spl6_4
  <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f123,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | spl6_3
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f101,f119])).

fof(f119,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f101,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f120,plain,
    ( spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f113,f96,f117])).

fof(f96,plain,
    ( spl6_2
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f113,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ spl6_2 ),
    inference(resolution,[],[f98,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK0,sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f110,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl6_1
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f102,f85,f102,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(definition_unfolding,[],[f31,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f85,plain,
    ( k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_1
  <=> k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f102,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f103,plain,
    ( spl6_2
    | spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f93,f83,f100,f96])).

fof(f93,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK0,sK0))
    | spl6_1 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK0,sK0))
    | spl6_1 ),
    inference(factoring,[],[f89])).

fof(f89,plain,
    ( ! [X2] :
        ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),X2),k1_enumset1(sK0,sK1,sK2))
        | k1_enumset1(sK0,sK1,sK2) != X2
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),X2),X2)
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),X2),k1_enumset1(sK0,sK0,sK0)) )
    | spl6_1 ),
    inference(superposition,[],[f85,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f86,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f54,f83])).

fof(f54,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f19,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f42,f26,f51])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (6472)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.49  % (6494)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (6494)Refutation not found, incomplete strategy% (6494)------------------------------
% 0.20/0.50  % (6494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6494)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6494)Memory used [KB]: 1663
% 0.20/0.50  % (6494)Time elapsed: 0.068 s
% 0.20/0.50  % (6494)------------------------------
% 0.20/0.50  % (6494)------------------------------
% 0.20/0.50  % (6474)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (6472)Refutation not found, incomplete strategy% (6472)------------------------------
% 0.20/0.50  % (6472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6480)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (6472)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6472)Memory used [KB]: 10746
% 0.20/0.50  % (6472)Time elapsed: 0.083 s
% 0.20/0.50  % (6472)------------------------------
% 0.20/0.50  % (6472)------------------------------
% 0.20/0.51  % (6480)Refutation not found, incomplete strategy% (6480)------------------------------
% 0.20/0.51  % (6480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6480)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6480)Memory used [KB]: 10618
% 0.20/0.51  % (6480)Time elapsed: 0.099 s
% 0.20/0.51  % (6480)------------------------------
% 0.20/0.51  % (6480)------------------------------
% 0.20/0.51  % (6493)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (6476)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (6493)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f86,f103,f110,f120,f136,f140])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    spl6_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f137])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    $false | spl6_5),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f80,f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) | spl6_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f133])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl6_5 <=> r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X4,X2,X1] : (r2_hidden(X4,k1_enumset1(X4,X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k1_enumset1(X4,X1,X2) != X3) )),
% 0.20/0.51    inference(equality_resolution,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    ~spl6_5 | spl6_3 | ~spl6_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f123,f117,f100,f133])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    spl6_3 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    spl6_4 <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) | (spl6_3 | ~spl6_4)),
% 0.20/0.51    inference(backward_demodulation,[],[f101,f119])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)) | ~spl6_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f117])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) | spl6_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f100])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    spl6_4 | ~spl6_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f113,f96,f117])).
% 0.20/0.51  fof(f96,plain,(
% 0.20/0.51    spl6_2 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)) | ~spl6_2),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)) | ~spl6_2),
% 0.20/0.51    inference(resolution,[],[f98,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.20/0.51    inference(equality_resolution,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK0,sK0)) | ~spl6_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f96])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl6_1 | ~spl6_3),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    $false | (spl6_1 | ~spl6_3)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f102,f85,f102,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f31,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))) | spl6_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f83])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    spl6_1 <=> k1_enumset1(sK0,sK1,sK2) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) | ~spl6_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f100])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    spl6_2 | spl6_3 | spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f93,f83,f100,f96])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK0,sK0)) | spl6_1),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f92])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK0,sK0)) | spl6_1),
% 0.20/0.51    inference(factoring,[],[f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X2] : (r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),X2),k1_enumset1(sK0,sK1,sK2)) | k1_enumset1(sK0,sK1,sK2) != X2 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),X2),X2) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK1,sK2),X2),k1_enumset1(sK0,sK0,sK0))) ) | spl6_1),
% 0.20/0.51    inference(superposition,[],[f85,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f32,f26])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k2_xboole_0(X0,X1) = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ~spl6_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f54,f83])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f42,f26,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f22,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.51    inference(negated_conjecture,[],[f15])).
% 0.20/0.51  fof(f15,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (6493)------------------------------
% 0.20/0.51  % (6493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6493)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (6493)Memory used [KB]: 10746
% 0.20/0.51  % (6493)Time elapsed: 0.098 s
% 0.20/0.51  % (6493)------------------------------
% 0.20/0.51  % (6493)------------------------------
% 0.20/0.51  % (6466)Success in time 0.152 s
%------------------------------------------------------------------------------
