%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:42 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 245 expanded)
%              Number of leaves         :   23 (  95 expanded)
%              Depth                    :   11
%              Number of atoms          :  196 ( 395 expanded)
%              Number of equality atoms :   73 ( 215 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f89,f90,f106,f108,f114,f122,f141,f150,f189,f196,f199])).

fof(f199,plain,
    ( spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f197,f193,f143])).

fof(f143,plain,
    ( spl5_10
  <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f193,plain,
    ( spl5_14
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f197,plain,
    ( r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f195,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f33,f53])).

fof(f53,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f195,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f196,plain,
    ( spl5_3
    | spl5_14
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f191,f186,f193,f85])).

fof(f85,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f186,plain,
    ( spl5_13
  <=> sK1 = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f191,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ spl5_13 ),
    inference(superposition,[],[f25,f188])).

fof(f188,plain,
    ( sK1 = sK2(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f189,plain,
    ( spl5_13
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f184,f138,f186])).

fof(f138,plain,
    ( spl5_9
  <=> r2_hidden(sK2(sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f184,plain,
    ( sK1 = sK2(sK0)
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( sK1 = sK2(sK0)
    | sK1 = sK2(sK0)
    | sK1 = sK2(sK0)
    | ~ spl5_9 ),
    inference(resolution,[],[f75,f140])).

fof(f140,plain,
    ( r2_hidden(sK2(sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f150,plain,
    ( ~ spl5_1
    | ~ spl5_10
    | spl5_2 ),
    inference(avatar_split_clause,[],[f148,f81,f143,f77])).

fof(f77,plain,
    ( spl5_1
  <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f81,plain,
    ( spl5_2
  <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f148,plain,
    ( ~ r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | ~ r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl5_2 ),
    inference(extensionality_resolution,[],[f29,f82])).

fof(f82,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f141,plain,
    ( spl5_3
    | spl5_9
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f135,f77,f138,f85])).

fof(f135,plain,
    ( r2_hidden(sK2(sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | k1_xboole_0 = sK0
    | ~ spl5_1 ),
    inference(resolution,[],[f79,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK2(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f30,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f79,plain,
    ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f122,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f113,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f113,plain,
    ( ~ r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_5
  <=> r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f114,plain,
    ( ~ spl5_5
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f109,f85,f77,f111])).

fof(f109,plain,
    ( ~ r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f78,f87])).

fof(f87,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f78,plain,
    ( ~ r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f108,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f105,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f105,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_4
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f106,plain,
    ( ~ spl5_4
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f101,f81,f77,f103])).

fof(f101,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_1
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f78,f83])).

fof(f83,plain,
    ( sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f90,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f56,f85,f77])).

fof(f56,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f20,f53])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f89,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f55,f81,f77])).

fof(f55,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f21,f53,f53])).

fof(f21,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,
    ( spl5_1
    | spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f54,f85,f81,f77])).

fof(f54,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f22,f53,f53])).

fof(f22,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (9292)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.57  % (9294)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (9284)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (9283)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.58  % (9293)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.65/0.58  % (9307)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.65/0.58  % (9300)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.65/0.58  % (9303)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.65/0.59  % (9296)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.65/0.59  % (9306)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.65/0.59  % (9294)Refutation not found, incomplete strategy% (9294)------------------------------
% 1.65/0.59  % (9294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (9304)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.65/0.59  % (9294)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (9294)Memory used [KB]: 10746
% 1.65/0.59  % (9294)Time elapsed: 0.144 s
% 1.65/0.59  % (9294)------------------------------
% 1.65/0.59  % (9294)------------------------------
% 1.65/0.59  % (9311)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.65/0.59  % (9288)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.65/0.59  % (9310)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.65/0.60  % (9293)Refutation not found, incomplete strategy% (9293)------------------------------
% 1.65/0.60  % (9293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.60  % (9291)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.65/0.60  % (9293)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.60  
% 1.65/0.60  % (9293)Memory used [KB]: 10618
% 1.65/0.60  % (9293)Time elapsed: 0.157 s
% 1.65/0.60  % (9293)------------------------------
% 1.65/0.60  % (9293)------------------------------
% 1.78/0.60  % (9313)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.78/0.60  % (9312)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.78/0.61  % (9300)Refutation found. Thanks to Tanya!
% 1.78/0.61  % SZS status Theorem for theBenchmark
% 1.78/0.61  % SZS output start Proof for theBenchmark
% 1.78/0.61  fof(f200,plain,(
% 1.78/0.61    $false),
% 1.78/0.61    inference(avatar_sat_refutation,[],[f88,f89,f90,f106,f108,f114,f122,f141,f150,f189,f196,f199])).
% 1.78/0.61  fof(f199,plain,(
% 1.78/0.61    spl5_10 | ~spl5_14),
% 1.78/0.61    inference(avatar_split_clause,[],[f197,f193,f143])).
% 1.78/0.61  fof(f143,plain,(
% 1.78/0.61    spl5_10 <=> r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.78/0.61  fof(f193,plain,(
% 1.78/0.61    spl5_14 <=> r2_hidden(sK1,sK0)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.78/0.61  fof(f197,plain,(
% 1.78/0.61    r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~spl5_14),
% 1.78/0.61    inference(resolution,[],[f195,f58])).
% 1.78/0.61  fof(f58,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f33,f53])).
% 1.78/0.61  fof(f53,plain,(
% 1.78/0.61    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f24,f52])).
% 1.78/0.61  fof(f52,plain,(
% 1.78/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f26,f51])).
% 1.78/0.61  fof(f51,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f35,f50])).
% 1.78/0.61  fof(f50,plain,(
% 1.78/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f36,f49])).
% 1.78/0.61  fof(f49,plain,(
% 1.78/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f45,f48])).
% 1.78/0.61  fof(f48,plain,(
% 1.78/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.78/0.61    inference(definition_unfolding,[],[f46,f47])).
% 1.78/0.61  fof(f47,plain,(
% 1.78/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f12])).
% 1.78/0.61  fof(f12,axiom,(
% 1.78/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.78/0.61  fof(f46,plain,(
% 1.78/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f11])).
% 1.78/0.61  fof(f11,axiom,(
% 1.78/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.78/0.61  fof(f45,plain,(
% 1.78/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f10])).
% 1.78/0.61  fof(f10,axiom,(
% 1.78/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.78/0.61  fof(f36,plain,(
% 1.78/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f9])).
% 1.78/0.61  fof(f9,axiom,(
% 1.78/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.78/0.61  fof(f35,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f8])).
% 1.78/0.61  fof(f8,axiom,(
% 1.78/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.78/0.61  fof(f26,plain,(
% 1.78/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f7])).
% 1.78/0.61  fof(f7,axiom,(
% 1.78/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.78/0.61  fof(f24,plain,(
% 1.78/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f6])).
% 1.78/0.61  fof(f6,axiom,(
% 1.78/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.78/0.61  fof(f33,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f13])).
% 1.78/0.61  fof(f13,axiom,(
% 1.78/0.61    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.78/0.61  fof(f195,plain,(
% 1.78/0.61    r2_hidden(sK1,sK0) | ~spl5_14),
% 1.78/0.61    inference(avatar_component_clause,[],[f193])).
% 1.78/0.61  fof(f196,plain,(
% 1.78/0.61    spl5_3 | spl5_14 | ~spl5_13),
% 1.78/0.61    inference(avatar_split_clause,[],[f191,f186,f193,f85])).
% 1.78/0.61  fof(f85,plain,(
% 1.78/0.61    spl5_3 <=> k1_xboole_0 = sK0),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.78/0.61  fof(f186,plain,(
% 1.78/0.61    spl5_13 <=> sK1 = sK2(sK0)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.78/0.61  fof(f191,plain,(
% 1.78/0.61    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0 | ~spl5_13),
% 1.78/0.61    inference(superposition,[],[f25,f188])).
% 1.78/0.61  fof(f188,plain,(
% 1.78/0.61    sK1 = sK2(sK0) | ~spl5_13),
% 1.78/0.61    inference(avatar_component_clause,[],[f186])).
% 1.78/0.61  fof(f25,plain,(
% 1.78/0.61    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.78/0.61    inference(cnf_transformation,[],[f17])).
% 1.78/0.61  fof(f17,plain,(
% 1.78/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.78/0.61    inference(ennf_transformation,[],[f2])).
% 1.78/0.61  fof(f2,axiom,(
% 1.78/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.78/0.61  fof(f189,plain,(
% 1.78/0.61    spl5_13 | ~spl5_9),
% 1.78/0.61    inference(avatar_split_clause,[],[f184,f138,f186])).
% 1.78/0.61  fof(f138,plain,(
% 1.78/0.61    spl5_9 <=> r2_hidden(sK2(sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.78/0.61  fof(f184,plain,(
% 1.78/0.61    sK1 = sK2(sK0) | ~spl5_9),
% 1.78/0.61    inference(duplicate_literal_removal,[],[f181])).
% 1.78/0.61  fof(f181,plain,(
% 1.78/0.61    sK1 = sK2(sK0) | sK1 = sK2(sK0) | sK1 = sK2(sK0) | ~spl5_9),
% 1.78/0.61    inference(resolution,[],[f75,f140])).
% 1.78/0.61  fof(f140,plain,(
% 1.78/0.61    r2_hidden(sK2(sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl5_9),
% 1.78/0.61    inference(avatar_component_clause,[],[f138])).
% 1.78/0.61  fof(f75,plain,(
% 1.78/0.61    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.78/0.61    inference(equality_resolution,[],[f62])).
% 1.78/0.61  fof(f62,plain,(
% 1.78/0.61    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.78/0.61    inference(definition_unfolding,[],[f41,f51])).
% 1.78/0.61  fof(f41,plain,(
% 1.78/0.61    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.78/0.61    inference(cnf_transformation,[],[f19])).
% 1.78/0.61  fof(f19,plain,(
% 1.78/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.78/0.61    inference(ennf_transformation,[],[f5])).
% 1.78/0.61  fof(f5,axiom,(
% 1.78/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.78/0.61  fof(f150,plain,(
% 1.78/0.61    ~spl5_1 | ~spl5_10 | spl5_2),
% 1.78/0.61    inference(avatar_split_clause,[],[f148,f81,f143,f77])).
% 1.78/0.61  fof(f77,plain,(
% 1.78/0.61    spl5_1 <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.78/0.61  fof(f81,plain,(
% 1.78/0.61    spl5_2 <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.78/0.61  fof(f148,plain,(
% 1.78/0.61    ~r1_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | ~r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl5_2),
% 1.78/0.61    inference(extensionality_resolution,[],[f29,f82])).
% 1.78/0.61  fof(f82,plain,(
% 1.78/0.61    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | spl5_2),
% 1.78/0.61    inference(avatar_component_clause,[],[f81])).
% 1.78/0.61  fof(f29,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.78/0.61    inference(cnf_transformation,[],[f3])).
% 1.78/0.61  fof(f3,axiom,(
% 1.78/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.78/0.61  fof(f141,plain,(
% 1.78/0.61    spl5_3 | spl5_9 | ~spl5_1),
% 1.78/0.61    inference(avatar_split_clause,[],[f135,f77,f138,f85])).
% 1.78/0.61  fof(f135,plain,(
% 1.78/0.61    r2_hidden(sK2(sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | k1_xboole_0 = sK0 | ~spl5_1),
% 1.78/0.61    inference(resolution,[],[f79,f97])).
% 1.78/0.61  fof(f97,plain,(
% 1.78/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(sK2(X0),X1) | k1_xboole_0 = X0) )),
% 1.78/0.61    inference(resolution,[],[f30,f25])).
% 1.78/0.61  fof(f30,plain,(
% 1.78/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f18])).
% 1.78/0.61  fof(f18,plain,(
% 1.78/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.78/0.61    inference(ennf_transformation,[],[f1])).
% 1.78/0.61  fof(f1,axiom,(
% 1.78/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.78/0.61  fof(f79,plain,(
% 1.78/0.61    r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl5_1),
% 1.78/0.61    inference(avatar_component_clause,[],[f77])).
% 1.78/0.61  fof(f122,plain,(
% 1.78/0.61    spl5_5),
% 1.78/0.61    inference(avatar_contradiction_clause,[],[f121])).
% 1.78/0.61  fof(f121,plain,(
% 1.78/0.61    $false | spl5_5),
% 1.78/0.61    inference(resolution,[],[f113,f23])).
% 1.78/0.61  fof(f23,plain,(
% 1.78/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.78/0.61    inference(cnf_transformation,[],[f4])).
% 1.78/0.61  fof(f4,axiom,(
% 1.78/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.78/0.61  fof(f113,plain,(
% 1.78/0.61    ~r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl5_5),
% 1.78/0.61    inference(avatar_component_clause,[],[f111])).
% 1.78/0.61  fof(f111,plain,(
% 1.78/0.61    spl5_5 <=> r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.78/0.61  fof(f114,plain,(
% 1.78/0.61    ~spl5_5 | spl5_1 | ~spl5_3),
% 1.78/0.61    inference(avatar_split_clause,[],[f109,f85,f77,f111])).
% 1.78/0.61  fof(f109,plain,(
% 1.78/0.61    ~r1_tarski(k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | (spl5_1 | ~spl5_3)),
% 1.78/0.61    inference(forward_demodulation,[],[f78,f87])).
% 1.78/0.61  fof(f87,plain,(
% 1.78/0.61    k1_xboole_0 = sK0 | ~spl5_3),
% 1.78/0.61    inference(avatar_component_clause,[],[f85])).
% 1.78/0.61  fof(f78,plain,(
% 1.78/0.61    ~r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl5_1),
% 1.78/0.61    inference(avatar_component_clause,[],[f77])).
% 1.78/0.61  fof(f108,plain,(
% 1.78/0.61    spl5_4),
% 1.78/0.61    inference(avatar_contradiction_clause,[],[f107])).
% 1.78/0.61  fof(f107,plain,(
% 1.78/0.61    $false | spl5_4),
% 1.78/0.61    inference(resolution,[],[f105,f67])).
% 1.78/0.61  fof(f67,plain,(
% 1.78/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.78/0.61    inference(equality_resolution,[],[f28])).
% 1.78/0.61  fof(f28,plain,(
% 1.78/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.78/0.61    inference(cnf_transformation,[],[f3])).
% 1.78/0.61  fof(f105,plain,(
% 1.78/0.61    ~r1_tarski(sK0,sK0) | spl5_4),
% 1.78/0.61    inference(avatar_component_clause,[],[f103])).
% 1.78/0.61  fof(f103,plain,(
% 1.78/0.61    spl5_4 <=> r1_tarski(sK0,sK0)),
% 1.78/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.78/0.61  fof(f106,plain,(
% 1.78/0.61    ~spl5_4 | spl5_1 | ~spl5_2),
% 1.78/0.61    inference(avatar_split_clause,[],[f101,f81,f77,f103])).
% 1.78/0.61  fof(f101,plain,(
% 1.78/0.61    ~r1_tarski(sK0,sK0) | (spl5_1 | ~spl5_2)),
% 1.78/0.61    inference(backward_demodulation,[],[f78,f83])).
% 1.78/0.61  fof(f83,plain,(
% 1.78/0.61    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl5_2),
% 1.78/0.61    inference(avatar_component_clause,[],[f81])).
% 1.78/0.61  fof(f90,plain,(
% 1.78/0.61    ~spl5_1 | ~spl5_3),
% 1.78/0.61    inference(avatar_split_clause,[],[f56,f85,f77])).
% 1.78/0.61  fof(f56,plain,(
% 1.78/0.61    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.78/0.61    inference(definition_unfolding,[],[f20,f53])).
% 1.78/0.61  fof(f20,plain,(
% 1.78/0.61    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 1.78/0.61    inference(cnf_transformation,[],[f16])).
% 1.78/0.61  fof(f16,plain,(
% 1.78/0.61    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.78/0.61    inference(ennf_transformation,[],[f15])).
% 1.78/0.61  fof(f15,negated_conjecture,(
% 1.78/0.61    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.78/0.61    inference(negated_conjecture,[],[f14])).
% 1.78/0.61  fof(f14,conjecture,(
% 1.78/0.61    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.78/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 1.78/0.61  fof(f89,plain,(
% 1.78/0.61    ~spl5_1 | ~spl5_2),
% 1.78/0.61    inference(avatar_split_clause,[],[f55,f81,f77])).
% 1.78/0.61  fof(f55,plain,(
% 1.78/0.61    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.78/0.61    inference(definition_unfolding,[],[f21,f53,f53])).
% 1.78/0.61  fof(f21,plain,(
% 1.78/0.61    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 1.78/0.61    inference(cnf_transformation,[],[f16])).
% 1.78/0.61  fof(f88,plain,(
% 1.78/0.61    spl5_1 | spl5_2 | spl5_3),
% 1.78/0.61    inference(avatar_split_clause,[],[f54,f85,f81,f77])).
% 1.78/0.61  fof(f54,plain,(
% 1.78/0.61    k1_xboole_0 = sK0 | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.78/0.61    inference(definition_unfolding,[],[f22,f53,f53])).
% 1.78/0.61  fof(f22,plain,(
% 1.78/0.61    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 1.78/0.61    inference(cnf_transformation,[],[f16])).
% 1.78/0.61  % SZS output end Proof for theBenchmark
% 1.78/0.61  % (9300)------------------------------
% 1.78/0.61  % (9300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (9300)Termination reason: Refutation
% 1.78/0.61  
% 1.78/0.61  % (9300)Memory used [KB]: 10746
% 1.78/0.61  % (9300)Time elapsed: 0.191 s
% 1.78/0.61  % (9300)------------------------------
% 1.78/0.61  % (9300)------------------------------
% 1.78/0.61  % (9279)Success in time 0.24 s
%------------------------------------------------------------------------------
