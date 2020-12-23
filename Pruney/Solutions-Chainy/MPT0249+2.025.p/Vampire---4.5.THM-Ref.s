%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 260 expanded)
%              Number of leaves         :   21 (  93 expanded)
%              Depth                    :   14
%              Number of atoms          :  198 ( 493 expanded)
%              Number of equality atoms :   68 ( 258 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f124,f130,f136,f147,f165,f175,f189])).

fof(f189,plain,
    ( ~ spl7_4
    | ~ spl7_6
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f174,f129,f178])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(sK1,X1) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(sK1,X1)
        | r1_tarski(sK1,X1) )
    | ~ spl7_4 ),
    inference(superposition,[],[f37,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK1,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f111,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f111,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | sK0 = X1 )
    | ~ spl7_4 ),
    inference(resolution,[],[f104,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f104,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl7_4 ),
    inference(superposition,[],[f74,f94])).

fof(f94,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl7_4
  <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f51])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f129,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_6
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f174,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_11
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f175,plain,
    ( spl7_1
    | ~ spl7_11
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f166,f162,f172,f77])).

fof(f77,plain,
    ( spl7_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f162,plain,
    ( spl7_10
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f166,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2
    | ~ spl7_10 ),
    inference(resolution,[],[f164,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f164,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f165,plain,
    ( spl7_10
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f159,f144,f92,f162])).

fof(f144,plain,
    ( spl7_9
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f159,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(resolution,[],[f151,f146])).

fof(f146,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f151,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(sK2,X1) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r1_tarski(sK2,X1)
        | r1_tarski(sK2,X1) )
    | ~ spl7_4 ),
    inference(superposition,[],[f37,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( sK0 = sK4(sK2,X0)
        | r1_tarski(sK2,X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f107,f36])).

fof(f107,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | sK0 = X1 )
    | ~ spl7_4 ),
    inference(resolution,[],[f103,f70])).

fof(f103,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl7_4 ),
    inference(superposition,[],[f73,f94])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f52])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f147,plain,
    ( spl7_2
    | spl7_9
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f142,f133,f144,f82])).

fof(f82,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f133,plain,
    ( spl7_7
  <=> sK0 = sK3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f142,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl7_7 ),
    inference(superposition,[],[f26,f135])).

fof(f135,plain,
    ( sK0 = sK3(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f136,plain,
    ( spl7_2
    | spl7_7
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f117,f92,f133,f82])).

fof(f117,plain,
    ( sK0 = sK3(sK1)
    | k1_xboole_0 = sK1
    | ~ spl7_4 ),
    inference(resolution,[],[f111,f26])).

fof(f130,plain,
    ( spl7_3
    | spl7_6
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f125,f121,f127,f87])).

fof(f87,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f121,plain,
    ( spl7_5
  <=> sK0 = sK3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f125,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_5 ),
    inference(superposition,[],[f26,f123])).

fof(f123,plain,
    ( sK0 = sK3(sK2)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f124,plain,
    ( spl7_3
    | spl7_5
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f114,f92,f121,f87])).

fof(f114,plain,
    ( sK0 = sK3(sK2)
    | k1_xboole_0 = sK2
    | ~ spl7_4 ),
    inference(resolution,[],[f107,f26])).

fof(f95,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f54,f92])).

fof(f54,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f20,f53,f52])).

fof(f20,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f90,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f23,f87])).

fof(f23,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f85,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f22,f82])).

fof(f22,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f21,f77])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (4715)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.47  % (4707)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.48  % (4715)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f190,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f124,f130,f136,f147,f165,f175,f189])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    ~spl7_4 | ~spl7_6 | spl7_11),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f180])).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    $false | (~spl7_4 | ~spl7_6 | spl7_11)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f174,f129,f178])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(sK1,X1)) ) | ~spl7_4),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f177])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(sK1,X1) | r1_tarski(sK1,X1)) ) | ~spl7_4),
% 0.20/0.48    inference(superposition,[],[f37,f118])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X0] : (sK0 = sK4(sK1,X0) | r1_tarski(sK1,X0)) ) | ~spl7_4),
% 0.20/0.48    inference(resolution,[],[f111,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,sK1) | sK0 = X1) ) | ~spl7_4),
% 0.20/0.48    inference(resolution,[],[f104,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,k3_enumset1(X0,X0,X0,X0,X0)) | X0 = X2) )),
% 0.20/0.48    inference(equality_resolution,[],[f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 0.20/0.48    inference(definition_unfolding,[],[f39,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f25,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f29,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f42,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ( ! [X4] : (r2_hidden(X4,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X4,sK1)) ) | ~spl7_4),
% 0.20/0.48    inference(superposition,[],[f74,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) | ~spl7_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl7_4 <=> k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X3,X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.48    inference(definition_unfolding,[],[f47,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f28,f51])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    r2_hidden(sK0,sK2) | ~spl7_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f127])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    spl7_6 <=> r2_hidden(sK0,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ~r1_tarski(sK1,sK2) | spl7_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f172])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    spl7_11 <=> r1_tarski(sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    spl7_1 | ~spl7_11 | ~spl7_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f166,f162,f172,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl7_1 <=> sK1 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    spl7_10 <=> r1_tarski(sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.48  fof(f166,plain,(
% 0.20/0.48    ~r1_tarski(sK1,sK2) | sK1 = sK2 | ~spl7_10),
% 0.20/0.48    inference(resolution,[],[f164,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    r1_tarski(sK2,sK1) | ~spl7_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f162])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    spl7_10 | ~spl7_4 | ~spl7_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f159,f144,f92,f162])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    spl7_9 <=> r2_hidden(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    r1_tarski(sK2,sK1) | (~spl7_4 | ~spl7_9)),
% 0.20/0.48    inference(resolution,[],[f151,f146])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    r2_hidden(sK0,sK1) | ~spl7_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f144])).
% 0.20/0.48  fof(f151,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(sK2,X1)) ) | ~spl7_4),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f150])).
% 0.20/0.48  fof(f150,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(sK0,X1) | r1_tarski(sK2,X1) | r1_tarski(sK2,X1)) ) | ~spl7_4),
% 0.20/0.48    inference(superposition,[],[f37,f115])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X0] : (sK0 = sK4(sK2,X0) | r1_tarski(sK2,X0)) ) | ~spl7_4),
% 0.20/0.48    inference(resolution,[],[f107,f36])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,sK2) | sK0 = X1) ) | ~spl7_4),
% 0.20/0.48    inference(resolution,[],[f103,f70])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ( ! [X3] : (r2_hidden(X3,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X3,sK2)) ) | ~spl7_4),
% 0.20/0.48    inference(superposition,[],[f73,f94])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X3,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 0.20/0.48    inference(definition_unfolding,[],[f48,f52])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    spl7_2 | spl7_9 | ~spl7_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f142,f133,f144,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl7_2 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl7_7 <=> sK0 = sK3(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1 | ~spl7_7),
% 0.20/0.48    inference(superposition,[],[f26,f135])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    sK0 = sK3(sK1) | ~spl7_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f133])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    spl7_2 | spl7_7 | ~spl7_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f117,f92,f133,f82])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    sK0 = sK3(sK1) | k1_xboole_0 = sK1 | ~spl7_4),
% 0.20/0.48    inference(resolution,[],[f111,f26])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl7_3 | spl7_6 | ~spl7_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f125,f121,f127,f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl7_3 <=> k1_xboole_0 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    spl7_5 <=> sK0 = sK3(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2 | ~spl7_5),
% 0.20/0.48    inference(superposition,[],[f26,f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    sK0 = sK3(sK2) | ~spl7_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f121])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    spl7_3 | spl7_5 | ~spl7_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f114,f92,f121,f87])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    sK0 = sK3(sK2) | k1_xboole_0 = sK2 | ~spl7_4),
% 0.20/0.48    inference(resolution,[],[f107,f26])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl7_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f54,f92])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.20/0.48    inference(definition_unfolding,[],[f20,f53,f52])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.48    inference(negated_conjecture,[],[f15])).
% 0.20/0.48  fof(f15,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~spl7_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f87])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    k1_xboole_0 != sK2),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ~spl7_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f82])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    k1_xboole_0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ~spl7_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f77])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    sK1 != sK2),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (4715)------------------------------
% 0.20/0.48  % (4715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (4715)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (4715)Memory used [KB]: 10746
% 0.20/0.48  % (4715)Time elapsed: 0.072 s
% 0.20/0.48  % (4715)------------------------------
% 0.20/0.48  % (4715)------------------------------
% 0.20/0.49  % (4691)Success in time 0.136 s
%------------------------------------------------------------------------------
