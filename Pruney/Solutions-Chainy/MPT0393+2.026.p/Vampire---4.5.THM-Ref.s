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
% DateTime   : Thu Dec  3 12:45:55 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 147 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 ( 286 expanded)
%              Number of equality atoms :   71 ( 135 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1724,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f105,f137,f1582,f1593,f1610,f1656])).

fof(f1656,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f1655])).

fof(f1655,plain,
    ( $false
    | ~ spl5_6 ),
    inference(trivial_inequality_removal,[],[f1628])).

fof(f1628,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_6 ),
    inference(superposition,[],[f262,f1577])).

fof(f1577,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f1575])).

fof(f1575,plain,
    ( spl5_6
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f262,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(backward_demodulation,[],[f68,f248])).

fof(f248,plain,(
    ! [X21] : k1_xboole_0 = k4_xboole_0(X21,X21) ),
    inference(resolution,[],[f180,f87])).

fof(f87,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f86,f70])).

fof(f70,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_enumset1(X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f75,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f180,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1
      | r2_hidden(sK4(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(resolution,[],[f45,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f34,f53,f53,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f52])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f1610,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1609])).

fof(f1609,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f1592,f66])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1592,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f1590])).

fof(f1590,plain,
    ( spl5_8
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1593,plain,
    ( spl5_3
    | spl5_6
    | ~ spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f1587,f1579,f1590,f1575,f101])).

fof(f101,plain,
    ( spl5_3
  <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1579,plain,
    ( spl5_7
  <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f1587,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl5_7 ),
    inference(superposition,[],[f26,f1581])).

fof(f1581,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f1579])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f1582,plain,
    ( spl5_6
    | spl5_7
    | spl5_3 ),
    inference(avatar_split_clause,[],[f1573,f101,f1579,f1575])).

fof(f1573,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl5_3 ),
    inference(duplicate_literal_removal,[],[f1561])).

fof(f1561,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | spl5_3 ),
    inference(resolution,[],[f141,f103])).

fof(f103,plain,
    ( ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f141,plain,(
    ! [X8,X7,X9] :
      ( r1_tarski(X9,k1_setfam_1(k2_enumset1(X8,X8,X8,X7)))
      | sK1(k2_enumset1(X8,X8,X8,X7),X9) = X8
      | k1_xboole_0 = k2_enumset1(X8,X8,X8,X7)
      | sK1(k2_enumset1(X8,X8,X8,X7),X9) = X7 ) ),
    inference(resolution,[],[f73,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f137,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f130,f99])).

fof(f99,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_2
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f130,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) ),
    inference(resolution,[],[f112,f66])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X0)),X1) ) ),
    inference(resolution,[],[f36,f70])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(k1_setfam_1(X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f105,plain,
    ( ~ spl5_3
    | ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f94,f79,f97,f101])).

fof(f79,plain,
    ( spl5_1
  <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f94,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl5_1 ),
    inference(extensionality_resolution,[],[f29,f81])).

fof(f81,plain,
    ( sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f82,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f54,f79])).

fof(f54,plain,(
    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f21,f53])).

fof(f21,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:16:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (9499)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (9499)Refutation not found, incomplete strategy% (9499)------------------------------
% 0.22/0.53  % (9499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9507)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (9499)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9499)Memory used [KB]: 10618
% 0.22/0.53  % (9499)Time elapsed: 0.083 s
% 0.22/0.53  % (9499)------------------------------
% 0.22/0.53  % (9499)------------------------------
% 0.22/0.53  % (9493)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (9493)Refutation not found, incomplete strategy% (9493)------------------------------
% 0.22/0.53  % (9493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9493)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9493)Memory used [KB]: 10618
% 0.22/0.53  % (9493)Time elapsed: 0.081 s
% 0.22/0.53  % (9493)------------------------------
% 0.22/0.53  % (9493)------------------------------
% 1.21/0.54  % (9504)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.21/0.54  % (9512)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.21/0.54  % (9512)Refutation not found, incomplete strategy% (9512)------------------------------
% 1.21/0.54  % (9512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.54  % (9512)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.54  
% 1.21/0.54  % (9512)Memory used [KB]: 1663
% 1.21/0.54  % (9512)Time elapsed: 0.132 s
% 1.21/0.54  % (9512)------------------------------
% 1.21/0.54  % (9512)------------------------------
% 1.21/0.55  % (9496)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.48/0.55  % (9501)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.48/0.56  % (9500)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.56  % (9505)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.56  % (9509)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.48/0.56  % (9517)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.57  % (9494)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.57  % (9511)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.57  % (9511)Refutation not found, incomplete strategy% (9511)------------------------------
% 1.48/0.57  % (9511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (9511)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (9511)Memory used [KB]: 10746
% 1.48/0.57  % (9511)Time elapsed: 0.162 s
% 1.48/0.57  % (9511)------------------------------
% 1.48/0.57  % (9511)------------------------------
% 1.48/0.58  % (9492)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.48/0.58  % (9514)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.58  % (9518)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.48/0.58  % (9514)Refutation not found, incomplete strategy% (9514)------------------------------
% 1.48/0.58  % (9514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (9514)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (9514)Memory used [KB]: 1663
% 1.48/0.58  % (9514)Time elapsed: 0.167 s
% 1.48/0.58  % (9514)------------------------------
% 1.48/0.58  % (9514)------------------------------
% 1.48/0.58  % (9519)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.48/0.58  % (9495)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.48/0.58  % (9503)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.58  % (9520)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.48/0.59  % (9510)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.59  % (9508)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.59  % (9516)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.59  % (9491)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.48/0.59  % (9502)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.60  % (9513)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.48/0.60  % (9506)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.48/0.61  % (9498)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.48/0.61  % (9491)Refutation not found, incomplete strategy% (9491)------------------------------
% 1.48/0.61  % (9491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.61  % (9491)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.61  
% 1.48/0.61  % (9491)Memory used [KB]: 1663
% 1.48/0.61  % (9491)Time elapsed: 0.177 s
% 1.48/0.61  % (9491)------------------------------
% 1.48/0.61  % (9491)------------------------------
% 1.48/0.61  % (9497)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.62  % (9551)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.48/0.62  % (9515)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.62  % (9551)Refutation not found, incomplete strategy% (9551)------------------------------
% 1.48/0.62  % (9551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.62  % (9551)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.62  
% 1.48/0.62  % (9551)Memory used [KB]: 6268
% 1.48/0.62  % (9551)Time elapsed: 0.026 s
% 1.48/0.62  % (9551)------------------------------
% 1.48/0.62  % (9551)------------------------------
% 1.48/0.63  % (9552)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.09/0.65  % (9507)Refutation found. Thanks to Tanya!
% 2.09/0.65  % SZS status Theorem for theBenchmark
% 2.09/0.65  % SZS output start Proof for theBenchmark
% 2.09/0.65  fof(f1724,plain,(
% 2.09/0.65    $false),
% 2.09/0.65    inference(avatar_sat_refutation,[],[f82,f105,f137,f1582,f1593,f1610,f1656])).
% 2.09/0.65  fof(f1656,plain,(
% 2.09/0.65    ~spl5_6),
% 2.09/0.65    inference(avatar_contradiction_clause,[],[f1655])).
% 2.09/0.65  fof(f1655,plain,(
% 2.09/0.65    $false | ~spl5_6),
% 2.09/0.65    inference(trivial_inequality_removal,[],[f1628])).
% 2.09/0.65  fof(f1628,plain,(
% 2.09/0.65    k1_xboole_0 != k1_xboole_0 | ~spl5_6),
% 2.09/0.65    inference(superposition,[],[f262,f1577])).
% 2.09/0.65  fof(f1577,plain,(
% 2.09/0.65    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl5_6),
% 2.09/0.65    inference(avatar_component_clause,[],[f1575])).
% 2.09/0.65  fof(f1575,plain,(
% 2.09/0.65    spl5_6 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.09/0.65  fof(f262,plain,(
% 2.09/0.65    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 2.09/0.65    inference(backward_demodulation,[],[f68,f248])).
% 2.09/0.65  fof(f248,plain,(
% 2.09/0.65    ( ! [X21] : (k1_xboole_0 = k4_xboole_0(X21,X21)) )),
% 2.09/0.65    inference(resolution,[],[f180,f87])).
% 2.09/0.65  fof(f87,plain,(
% 2.09/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.09/0.65    inference(resolution,[],[f86,f70])).
% 2.09/0.65  fof(f70,plain,(
% 2.09/0.65    ( ! [X0,X3] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X3))) )),
% 2.09/0.65    inference(equality_resolution,[],[f69])).
% 2.09/0.65  fof(f69,plain,(
% 2.09/0.65    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X3) != X2) )),
% 2.09/0.65    inference(equality_resolution,[],[f57])).
% 2.09/0.65  fof(f57,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.09/0.65    inference(definition_unfolding,[],[f42,f52])).
% 2.09/0.65  fof(f52,plain,(
% 2.09/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.09/0.65    inference(definition_unfolding,[],[f24,f35])).
% 2.09/0.65  fof(f35,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f8])).
% 2.09/0.65  fof(f8,axiom,(
% 2.09/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.09/0.65  fof(f24,plain,(
% 2.09/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f7])).
% 2.09/0.65  fof(f7,axiom,(
% 2.09/0.65    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.09/0.65  fof(f42,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f5])).
% 2.09/0.65  fof(f5,axiom,(
% 2.09/0.65    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.09/0.65  fof(f86,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 2.09/0.65    inference(superposition,[],[f75,f22])).
% 2.09/0.65  fof(f22,plain,(
% 2.09/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.09/0.65    inference(cnf_transformation,[],[f4])).
% 2.09/0.65  fof(f4,axiom,(
% 2.09/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.09/0.65  fof(f75,plain,(
% 2.09/0.65    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 2.09/0.65    inference(equality_resolution,[],[f47])).
% 2.09/0.65  fof(f47,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f2])).
% 2.09/0.65  fof(f2,axiom,(
% 2.09/0.65    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.09/0.65  fof(f180,plain,(
% 2.09/0.65    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f177])).
% 2.09/0.65  fof(f177,plain,(
% 2.09/0.65    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1 | r2_hidden(sK4(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 2.09/0.65    inference(resolution,[],[f45,f44])).
% 2.09/0.65  fof(f44,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f2])).
% 2.09/0.65  fof(f45,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f2])).
% 2.09/0.65  fof(f68,plain,(
% 2.09/0.65    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 2.09/0.65    inference(equality_resolution,[],[f55])).
% 2.09/0.65  fof(f55,plain,(
% 2.09/0.65    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 2.09/0.65    inference(definition_unfolding,[],[f34,f53,f53,f53])).
% 2.09/0.65  fof(f53,plain,(
% 2.09/0.65    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.09/0.65    inference(definition_unfolding,[],[f23,f52])).
% 2.09/0.65  fof(f23,plain,(
% 2.09/0.65    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f6])).
% 2.09/0.65  fof(f6,axiom,(
% 2.09/0.65    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.09/0.65  fof(f34,plain,(
% 2.09/0.65    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f9])).
% 2.09/0.65  fof(f9,axiom,(
% 2.09/0.65    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 2.09/0.65  fof(f1610,plain,(
% 2.09/0.65    spl5_8),
% 2.09/0.65    inference(avatar_contradiction_clause,[],[f1609])).
% 2.09/0.65  fof(f1609,plain,(
% 2.09/0.65    $false | spl5_8),
% 2.09/0.65    inference(resolution,[],[f1592,f66])).
% 2.09/0.65  fof(f66,plain,(
% 2.09/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.09/0.65    inference(equality_resolution,[],[f28])).
% 2.09/0.65  fof(f28,plain,(
% 2.09/0.65    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.09/0.65    inference(cnf_transformation,[],[f3])).
% 2.09/0.65  fof(f3,axiom,(
% 2.09/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.09/0.65  fof(f1592,plain,(
% 2.09/0.65    ~r1_tarski(sK0,sK0) | spl5_8),
% 2.09/0.65    inference(avatar_component_clause,[],[f1590])).
% 2.09/0.65  fof(f1590,plain,(
% 2.09/0.65    spl5_8 <=> r1_tarski(sK0,sK0)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.09/0.65  fof(f1593,plain,(
% 2.09/0.65    spl5_3 | spl5_6 | ~spl5_8 | ~spl5_7),
% 2.09/0.65    inference(avatar_split_clause,[],[f1587,f1579,f1590,f1575,f101])).
% 2.09/0.65  fof(f101,plain,(
% 2.09/0.65    spl5_3 <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.09/0.65  fof(f1579,plain,(
% 2.09/0.65    spl5_7 <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.09/0.65  fof(f1587,plain,(
% 2.09/0.65    ~r1_tarski(sK0,sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl5_7),
% 2.09/0.65    inference(superposition,[],[f26,f1581])).
% 2.09/0.65  fof(f1581,plain,(
% 2.09/0.65    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | ~spl5_7),
% 2.09/0.65    inference(avatar_component_clause,[],[f1579])).
% 2.09/0.65  fof(f26,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r1_tarski(X1,sK1(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f17])).
% 2.09/0.65  fof(f17,plain,(
% 2.09/0.65    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.09/0.65    inference(flattening,[],[f16])).
% 2.09/0.65  fof(f16,plain,(
% 2.09/0.65    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.09/0.65    inference(ennf_transformation,[],[f11])).
% 2.09/0.65  fof(f11,axiom,(
% 2.09/0.65    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 2.09/0.65  fof(f1582,plain,(
% 2.09/0.65    spl5_6 | spl5_7 | spl5_3),
% 2.09/0.65    inference(avatar_split_clause,[],[f1573,f101,f1579,f1575])).
% 2.09/0.65  fof(f1573,plain,(
% 2.09/0.65    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | spl5_3),
% 2.09/0.65    inference(duplicate_literal_removal,[],[f1561])).
% 2.09/0.65  fof(f1561,plain,(
% 2.09/0.65    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | spl5_3),
% 2.09/0.65    inference(resolution,[],[f141,f103])).
% 2.09/0.65  fof(f103,plain,(
% 2.09/0.65    ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_3),
% 2.09/0.65    inference(avatar_component_clause,[],[f101])).
% 2.09/0.65  fof(f141,plain,(
% 2.09/0.65    ( ! [X8,X7,X9] : (r1_tarski(X9,k1_setfam_1(k2_enumset1(X8,X8,X8,X7))) | sK1(k2_enumset1(X8,X8,X8,X7),X9) = X8 | k1_xboole_0 = k2_enumset1(X8,X8,X8,X7) | sK1(k2_enumset1(X8,X8,X8,X7),X9) = X7) )),
% 2.09/0.65    inference(resolution,[],[f73,f25])).
% 2.09/0.65  fof(f25,plain,(
% 2.09/0.65    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.09/0.65    inference(cnf_transformation,[],[f17])).
% 2.09/0.65  fof(f73,plain,(
% 2.09/0.65    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 2.09/0.65    inference(equality_resolution,[],[f59])).
% 2.09/0.65  fof(f59,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.09/0.65    inference(definition_unfolding,[],[f40,f52])).
% 2.09/0.65  fof(f40,plain,(
% 2.09/0.65    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.09/0.65    inference(cnf_transformation,[],[f5])).
% 2.09/0.65  fof(f137,plain,(
% 2.09/0.65    spl5_2),
% 2.09/0.65    inference(avatar_contradiction_clause,[],[f132])).
% 2.09/0.65  fof(f132,plain,(
% 2.09/0.65    $false | spl5_2),
% 2.09/0.65    inference(resolution,[],[f130,f99])).
% 2.09/0.65  fof(f99,plain,(
% 2.09/0.65    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | spl5_2),
% 2.09/0.65    inference(avatar_component_clause,[],[f97])).
% 2.09/0.65  fof(f97,plain,(
% 2.09/0.65    spl5_2 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.09/0.65  fof(f130,plain,(
% 2.09/0.65    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1)) )),
% 2.09/0.65    inference(resolution,[],[f112,f66])).
% 2.09/0.65  fof(f112,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X0)),X1)) )),
% 2.09/0.65    inference(resolution,[],[f36,f70])).
% 2.09/0.65  fof(f36,plain,(
% 2.09/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(k1_setfam_1(X1),X2)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f20])).
% 2.09/0.65  fof(f20,plain,(
% 2.09/0.65    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 2.09/0.65    inference(flattening,[],[f19])).
% 2.09/0.65  fof(f19,plain,(
% 2.09/0.65    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 2.09/0.65    inference(ennf_transformation,[],[f12])).
% 2.09/0.65  fof(f12,axiom,(
% 2.09/0.65    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 2.09/0.65  fof(f105,plain,(
% 2.09/0.65    ~spl5_3 | ~spl5_2 | spl5_1),
% 2.09/0.65    inference(avatar_split_clause,[],[f94,f79,f97,f101])).
% 2.09/0.65  fof(f79,plain,(
% 2.09/0.65    spl5_1 <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.09/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.09/0.65  fof(f94,plain,(
% 2.09/0.65    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl5_1),
% 2.09/0.65    inference(extensionality_resolution,[],[f29,f81])).
% 2.09/0.65  fof(f81,plain,(
% 2.09/0.65    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) | spl5_1),
% 2.09/0.65    inference(avatar_component_clause,[],[f79])).
% 2.09/0.65  fof(f29,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.09/0.65    inference(cnf_transformation,[],[f3])).
% 2.09/0.65  fof(f82,plain,(
% 2.09/0.65    ~spl5_1),
% 2.09/0.65    inference(avatar_split_clause,[],[f54,f79])).
% 2.09/0.65  fof(f54,plain,(
% 2.09/0.65    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.09/0.65    inference(definition_unfolding,[],[f21,f53])).
% 2.09/0.65  fof(f21,plain,(
% 2.09/0.65    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 2.09/0.65    inference(cnf_transformation,[],[f15])).
% 2.09/0.65  fof(f15,plain,(
% 2.09/0.65    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 2.09/0.65    inference(ennf_transformation,[],[f14])).
% 2.09/0.65  fof(f14,negated_conjecture,(
% 2.09/0.65    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.09/0.65    inference(negated_conjecture,[],[f13])).
% 2.09/0.65  fof(f13,conjecture,(
% 2.09/0.65    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.09/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 2.09/0.65  % SZS output end Proof for theBenchmark
% 2.09/0.65  % (9507)------------------------------
% 2.09/0.65  % (9507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.65  % (9507)Termination reason: Refutation
% 2.09/0.65  
% 2.09/0.65  % (9507)Memory used [KB]: 12665
% 2.09/0.65  % (9507)Time elapsed: 0.237 s
% 2.09/0.65  % (9507)------------------------------
% 2.09/0.65  % (9507)------------------------------
% 2.09/0.65  % (9490)Success in time 0.28 s
%------------------------------------------------------------------------------
