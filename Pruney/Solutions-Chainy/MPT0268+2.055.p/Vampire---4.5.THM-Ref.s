%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:43 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 146 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  168 ( 272 expanded)
%              Number of equality atoms :   77 ( 153 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f887,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f88,f111,f847,f885,f886])).

fof(f886,plain,
    ( sK1 != sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f885,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f874])).

fof(f874,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f78,f69,f869])).

fof(f869,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
        | ~ r2_hidden(X4,sK0) )
    | ~ spl4_1 ),
    inference(superposition,[],[f62,f73])).

fof(f73,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f69,plain,(
    ! [X4,X2,X1] : r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X4,X3)
      | k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f20,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 != X4
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f78,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f847,plain,
    ( spl4_4
    | ~ spl4_3
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f841,f108,f72,f108,f844])).

fof(f844,plain,
    ( spl4_4
  <=> sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f108,plain,
    ( spl4_3
  <=> r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f841,plain,
    ( ~ r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | spl4_1
    | ~ spl4_3 ),
    inference(trivial_inequality_removal,[],[f810])).

fof(f810,plain,
    ( ~ r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | sK0 != sK0
    | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f135,f110])).

fof(f110,plain,
    ( r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f135,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),sK0)
        | ~ r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),X1)
        | sK0 != X1
        | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1) )
    | spl4_1 ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( ! [X1] :
        ( sK0 != X1
        | ~ r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),X1)
        | ~ r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),sK0)
        | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1)
        | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1)
        | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1) )
    | spl4_1 ),
    inference(resolution,[],[f84,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f32,f42])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
        | sK0 != X0
        | ~ r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0),X0)
        | ~ r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0),sK0) )
    | spl4_1 ),
    inference(superposition,[],[f74,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f74,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f111,plain,
    ( spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f101,f72,f108])).

fof(f101,plain,
    ( r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,
    ( r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0)
    | sK0 != sK0
    | spl4_1 ),
    inference(factoring,[],[f85])).

fof(f85,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),sK0)
        | r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),X1)
        | sK0 != X1 )
    | spl4_1 ),
    inference(superposition,[],[f74,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f88,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f76,f72])).

fof(f46,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f15,f19,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f18,f42])).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f79,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f45,f76,f72])).

fof(f45,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f16,f19,f44])).

fof(f16,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:20:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (23292)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (23285)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (23300)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (23308)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (23304)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.57  % (23312)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (23288)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (23296)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (23303)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.59  % (23301)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.59  % (23311)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.59  % (23295)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.78/0.60  % (23290)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.78/0.60  % (23287)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.78/0.60  % (23289)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.78/0.61  % (23299)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.78/0.61  % (23287)Refutation not found, incomplete strategy% (23287)------------------------------
% 1.78/0.61  % (23287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (23287)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (23287)Memory used [KB]: 10618
% 1.78/0.61  % (23287)Time elapsed: 0.131 s
% 1.78/0.61  % (23287)------------------------------
% 1.78/0.61  % (23287)------------------------------
% 1.78/0.61  % (23307)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.78/0.61  % (23286)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.78/0.62  % (23293)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.78/0.62  % (23310)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.78/0.62  % (23313)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.00/0.62  % (23293)Refutation not found, incomplete strategy% (23293)------------------------------
% 2.00/0.62  % (23293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.62  % (23291)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.00/0.62  % (23309)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.00/0.62  % (23293)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.62  
% 2.00/0.62  % (23293)Memory used [KB]: 10618
% 2.00/0.62  % (23293)Time elapsed: 0.191 s
% 2.00/0.62  % (23293)------------------------------
% 2.00/0.62  % (23293)------------------------------
% 2.00/0.63  % (23305)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.00/0.63  % (23306)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.00/0.63  % (23306)Refutation not found, incomplete strategy% (23306)------------------------------
% 2.00/0.63  % (23306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.63  % (23306)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.63  
% 2.00/0.63  % (23306)Memory used [KB]: 1663
% 2.00/0.63  % (23306)Time elapsed: 0.203 s
% 2.00/0.63  % (23306)------------------------------
% 2.00/0.63  % (23306)------------------------------
% 2.00/0.63  % (23305)Refutation not found, incomplete strategy% (23305)------------------------------
% 2.00/0.63  % (23305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.63  % (23305)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.63  
% 2.00/0.63  % (23305)Memory used [KB]: 10746
% 2.00/0.63  % (23305)Time elapsed: 0.204 s
% 2.00/0.63  % (23305)------------------------------
% 2.00/0.63  % (23305)------------------------------
% 2.00/0.64  % (23314)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.00/0.64  % (23297)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.00/0.64  % (23298)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.00/0.65  % (23302)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.22/0.65  % (23302)Refutation not found, incomplete strategy% (23302)------------------------------
% 2.22/0.65  % (23302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.65  % (23302)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.65  
% 2.22/0.65  % (23302)Memory used [KB]: 10746
% 2.22/0.65  % (23302)Time elapsed: 0.212 s
% 2.22/0.65  % (23302)------------------------------
% 2.22/0.65  % (23302)------------------------------
% 2.22/0.65  % (23294)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.22/0.68  % (23307)Refutation found. Thanks to Tanya!
% 2.22/0.68  % SZS status Theorem for theBenchmark
% 2.22/0.70  % SZS output start Proof for theBenchmark
% 2.22/0.70  fof(f887,plain,(
% 2.22/0.70    $false),
% 2.22/0.70    inference(avatar_sat_refutation,[],[f79,f88,f111,f847,f885,f886])).
% 2.22/0.70  fof(f886,plain,(
% 2.22/0.70    sK1 != sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | r2_hidden(sK1,sK0) | ~r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0)),
% 2.22/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.22/0.70  fof(f885,plain,(
% 2.22/0.70    ~spl4_1 | ~spl4_2),
% 2.22/0.70    inference(avatar_contradiction_clause,[],[f874])).
% 2.22/0.70  fof(f874,plain,(
% 2.22/0.70    $false | (~spl4_1 | ~spl4_2)),
% 2.22/0.70    inference(unit_resulting_resolution,[],[f78,f69,f869])).
% 2.22/0.70  fof(f869,plain,(
% 2.22/0.70    ( ! [X4] : (~r2_hidden(X4,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X4,sK0)) ) | ~spl4_1),
% 2.22/0.70    inference(superposition,[],[f62,f73])).
% 2.22/0.70  fof(f73,plain,(
% 2.22/0.70    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl4_1),
% 2.22/0.70    inference(avatar_component_clause,[],[f72])).
% 2.22/0.70  fof(f72,plain,(
% 2.22/0.70    spl4_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.22/0.70  fof(f62,plain,(
% 2.22/0.70    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 2.22/0.70    inference(equality_resolution,[],[f48])).
% 2.22/0.70  fof(f48,plain,(
% 2.22/0.70    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.22/0.70    inference(definition_unfolding,[],[f25,f19])).
% 2.22/0.70  fof(f19,plain,(
% 2.22/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.22/0.70    inference(cnf_transformation,[],[f2])).
% 2.22/0.70  fof(f2,axiom,(
% 2.22/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.22/0.70  fof(f25,plain,(
% 2.22/0.70    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.22/0.70    inference(cnf_transformation,[],[f1])).
% 2.22/0.70  fof(f1,axiom,(
% 2.22/0.70    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.22/0.70  fof(f69,plain,(
% 2.22/0.70    ( ! [X4,X2,X1] : (r2_hidden(X4,k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2))) )),
% 2.22/0.70    inference(equality_resolution,[],[f68])).
% 2.22/0.70  fof(f68,plain,(
% 2.22/0.70    ( ! [X4,X2,X3,X1] : (r2_hidden(X4,X3) | k6_enumset1(X4,X4,X4,X4,X4,X4,X1,X2) != X3) )),
% 2.22/0.70    inference(equality_resolution,[],[f55])).
% 2.22/0.70  fof(f55,plain,(
% 2.22/0.70    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.22/0.70    inference(definition_unfolding,[],[f33,f42])).
% 2.22/0.70  fof(f42,plain,(
% 2.22/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.22/0.70    inference(definition_unfolding,[],[f20,f41])).
% 2.22/0.70  fof(f41,plain,(
% 2.22/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.22/0.70    inference(definition_unfolding,[],[f27,f40])).
% 2.22/0.70  fof(f40,plain,(
% 2.22/0.70    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.22/0.70    inference(definition_unfolding,[],[f36,f39])).
% 2.22/0.70  fof(f39,plain,(
% 2.22/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.22/0.70    inference(definition_unfolding,[],[f37,f38])).
% 2.22/0.70  fof(f38,plain,(
% 2.22/0.70    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.22/0.70    inference(cnf_transformation,[],[f10])).
% 2.22/0.70  fof(f10,axiom,(
% 2.22/0.70    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.22/0.70  fof(f37,plain,(
% 2.22/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.22/0.70    inference(cnf_transformation,[],[f9])).
% 2.22/0.70  fof(f9,axiom,(
% 2.22/0.70    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.22/0.70  fof(f36,plain,(
% 2.22/0.70    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.22/0.70    inference(cnf_transformation,[],[f8])).
% 2.22/0.70  fof(f8,axiom,(
% 2.22/0.70    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.22/0.70  fof(f27,plain,(
% 2.22/0.70    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.22/0.70    inference(cnf_transformation,[],[f7])).
% 2.22/0.70  fof(f7,axiom,(
% 2.22/0.70    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.22/0.70  fof(f20,plain,(
% 2.22/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.22/0.70    inference(cnf_transformation,[],[f6])).
% 2.22/0.70  fof(f6,axiom,(
% 2.22/0.70    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.22/0.70  fof(f33,plain,(
% 2.22/0.70    ( ! [X4,X2,X0,X3,X1] : (X0 != X4 | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.22/0.70    inference(cnf_transformation,[],[f14])).
% 2.22/0.70  fof(f14,plain,(
% 2.22/0.70    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.22/0.70    inference(ennf_transformation,[],[f3])).
% 2.22/0.70  fof(f3,axiom,(
% 2.22/0.70    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 2.22/0.70  fof(f78,plain,(
% 2.22/0.70    r2_hidden(sK1,sK0) | ~spl4_2),
% 2.22/0.70    inference(avatar_component_clause,[],[f76])).
% 2.22/0.70  fof(f76,plain,(
% 2.22/0.70    spl4_2 <=> r2_hidden(sK1,sK0)),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.22/0.70  fof(f847,plain,(
% 2.22/0.70    spl4_4 | ~spl4_3 | spl4_1 | ~spl4_3),
% 2.22/0.70    inference(avatar_split_clause,[],[f841,f108,f72,f108,f844])).
% 2.22/0.70  fof(f844,plain,(
% 2.22/0.70    spl4_4 <=> sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0)),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.22/0.70  fof(f108,plain,(
% 2.22/0.70    spl4_3 <=> r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0)),
% 2.22/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.22/0.70  fof(f841,plain,(
% 2.22/0.70    ~r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0) | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | (spl4_1 | ~spl4_3)),
% 2.22/0.70    inference(trivial_inequality_removal,[],[f810])).
% 2.22/0.70  fof(f810,plain,(
% 2.22/0.70    ~r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0) | sK0 != sK0 | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0) | (spl4_1 | ~spl4_3)),
% 2.22/0.70    inference(resolution,[],[f135,f110])).
% 2.22/0.70  fof(f110,plain,(
% 2.22/0.70    r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0) | ~spl4_3),
% 2.22/0.70    inference(avatar_component_clause,[],[f108])).
% 2.22/0.70  fof(f135,plain,(
% 2.22/0.70    ( ! [X1] : (~r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),sK0) | ~r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),X1) | sK0 != X1 | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1)) ) | spl4_1),
% 2.22/0.70    inference(duplicate_literal_removal,[],[f129])).
% 2.22/0.70  fof(f129,plain,(
% 2.22/0.70    ( ! [X1] : (sK0 != X1 | ~r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),X1) | ~r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),sK0) | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1) | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1) | sK1 = sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1)) ) | spl4_1),
% 2.22/0.70    inference(resolution,[],[f84,f70])).
% 2.22/0.70  fof(f70,plain,(
% 2.22/0.70    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 2.22/0.70    inference(equality_resolution,[],[f56])).
% 2.22/0.70  fof(f56,plain,(
% 2.22/0.70    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.22/0.70    inference(definition_unfolding,[],[f32,f42])).
% 2.22/0.70  fof(f32,plain,(
% 2.22/0.70    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.22/0.70    inference(cnf_transformation,[],[f14])).
% 2.22/0.70  fof(f84,plain,(
% 2.22/0.70    ( ! [X0] : (r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | sK0 != X0 | ~r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0),X0) | ~r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X0),sK0)) ) | spl4_1),
% 2.22/0.70    inference(superposition,[],[f74,f52])).
% 2.22/0.70  fof(f52,plain,(
% 2.22/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0)) )),
% 2.22/0.70    inference(definition_unfolding,[],[f21,f19])).
% 2.22/0.70  fof(f21,plain,(
% 2.22/0.70    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.22/0.70    inference(cnf_transformation,[],[f1])).
% 2.22/0.70  fof(f74,plain,(
% 2.22/0.70    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | spl4_1),
% 2.22/0.70    inference(avatar_component_clause,[],[f72])).
% 2.22/0.70  fof(f111,plain,(
% 2.22/0.70    spl4_3 | spl4_1),
% 2.22/0.70    inference(avatar_split_clause,[],[f101,f72,f108])).
% 2.22/0.70  fof(f101,plain,(
% 2.22/0.70    r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0) | spl4_1),
% 2.22/0.70    inference(trivial_inequality_removal,[],[f95])).
% 2.22/0.70  fof(f95,plain,(
% 2.22/0.70    r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK0),sK0) | sK0 != sK0 | spl4_1),
% 2.22/0.70    inference(factoring,[],[f85])).
% 2.22/0.70  fof(f85,plain,(
% 2.22/0.70    ( ! [X1] : (r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),sK0) | r2_hidden(sK2(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X1),X1) | sK0 != X1) ) | spl4_1),
% 2.22/0.70    inference(superposition,[],[f74,f51])).
% 2.22/0.70  fof(f51,plain,(
% 2.22/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0)) )),
% 2.22/0.70    inference(definition_unfolding,[],[f22,f19])).
% 2.22/0.70  fof(f22,plain,(
% 2.22/0.70    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.22/0.70    inference(cnf_transformation,[],[f1])).
% 2.22/0.70  fof(f88,plain,(
% 2.22/0.70    spl4_1 | ~spl4_2),
% 2.22/0.70    inference(avatar_split_clause,[],[f46,f76,f72])).
% 2.22/0.70  fof(f46,plain,(
% 2.22/0.70    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.70    inference(definition_unfolding,[],[f15,f19,f44])).
% 2.22/0.70  fof(f44,plain,(
% 2.22/0.70    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.22/0.70    inference(definition_unfolding,[],[f17,f43])).
% 2.22/0.70  fof(f43,plain,(
% 2.22/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.22/0.70    inference(definition_unfolding,[],[f18,f42])).
% 2.22/0.70  fof(f18,plain,(
% 2.22/0.70    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.22/0.70    inference(cnf_transformation,[],[f5])).
% 2.22/0.70  fof(f5,axiom,(
% 2.22/0.70    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.22/0.70  fof(f17,plain,(
% 2.22/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.22/0.70    inference(cnf_transformation,[],[f4])).
% 2.22/0.70  fof(f4,axiom,(
% 2.22/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.22/0.70  fof(f15,plain,(
% 2.22/0.70    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.22/0.70    inference(cnf_transformation,[],[f13])).
% 2.22/0.70  fof(f13,plain,(
% 2.22/0.70    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 2.22/0.70    inference(ennf_transformation,[],[f12])).
% 2.22/0.70  fof(f12,negated_conjecture,(
% 2.22/0.70    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.22/0.70    inference(negated_conjecture,[],[f11])).
% 2.22/0.70  fof(f11,conjecture,(
% 2.22/0.70    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.22/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.22/0.70  fof(f79,plain,(
% 2.22/0.70    ~spl4_1 | spl4_2),
% 2.22/0.70    inference(avatar_split_clause,[],[f45,f76,f72])).
% 2.22/0.70  fof(f45,plain,(
% 2.22/0.70    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.22/0.70    inference(definition_unfolding,[],[f16,f19,f44])).
% 2.22/0.70  fof(f16,plain,(
% 2.22/0.70    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.22/0.70    inference(cnf_transformation,[],[f13])).
% 2.22/0.70  % SZS output end Proof for theBenchmark
% 2.22/0.70  % (23307)------------------------------
% 2.22/0.70  % (23307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.70  % (23307)Termination reason: Refutation
% 2.22/0.70  
% 2.22/0.70  % (23307)Memory used [KB]: 11129
% 2.22/0.70  % (23307)Time elapsed: 0.189 s
% 2.22/0.70  % (23307)------------------------------
% 2.22/0.70  % (23307)------------------------------
% 2.22/0.70  % (23284)Success in time 0.337 s
%------------------------------------------------------------------------------
