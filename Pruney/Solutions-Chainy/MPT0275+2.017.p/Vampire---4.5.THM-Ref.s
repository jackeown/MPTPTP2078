%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:28 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 291 expanded)
%              Number of leaves         :   15 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  249 ( 667 expanded)
%              Number of equality atoms :   57 ( 214 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f716,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f65,f286,f372,f410,f420,f506,f508,f565,f567,f715])).

fof(f715,plain,
    ( ~ spl5_2
    | spl5_4
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | ~ spl5_2
    | spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f58,f705])).

fof(f705,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f281,f419])).

fof(f419,plain,
    ( sK1 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl5_8
  <=> sK1 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f281,plain,
    ( ~ r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl5_4
  <=> r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f58,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f567,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | ~ spl5_3
    | spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f63,f426])).

fof(f426,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_4
    | ~ spl5_7 ),
    inference(superposition,[],[f281,f415])).

fof(f415,plain,
    ( sK0 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl5_7
  <=> sK0 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f63,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f565,plain,(
    ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl5_18 ),
    inference(unit_resulting_resolution,[],[f67,f67,f67,f505,f334])).

fof(f334,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X2,X1,X1),X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | r2_hidden(sK4(X2,X1,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(sK4(X2,X1,X1),X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(sK4(X2,X1,X1),X1) ) ),
    inference(condensation,[],[f332])).

fof(f332,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(X4,X5)
      | ~ r2_hidden(X4,X6)
      | r2_hidden(sK4(X6,X5,X5),X6)
      | r2_hidden(X7,X5)
      | ~ r2_hidden(X7,X6)
      | r2_hidden(sK4(X6,X5,X5),X5) ) ),
    inference(duplicate_literal_removal,[],[f319])).

fof(f319,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(X4,X5)
      | ~ r2_hidden(X4,X6)
      | r2_hidden(X4,X5)
      | r2_hidden(sK4(X6,X5,X5),X6)
      | r2_hidden(X7,X5)
      | ~ r2_hidden(X7,X6)
      | r2_hidden(sK4(X6,X5,X5),X5)
      | r2_hidden(X7,X5) ) ),
    inference(resolution,[],[f88,f77])).

fof(f77,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK4(X2,X3,X4),X3)
      | r2_hidden(X5,X3)
      | ~ r2_hidden(X5,X2)
      | r2_hidden(sK4(X2,X3,X4),X4)
      | r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f48,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1) ) ),
    inference(definition_unfolding,[],[f23,f14])).

fof(f14,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
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

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f14])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f88,plain,(
    ! [X6,X8,X7,X9] :
      ( r2_hidden(sK4(X6,X7,X8),X8)
      | r2_hidden(X9,X7)
      | ~ r2_hidden(X9,X6)
      | r2_hidden(X9,X8)
      | r2_hidden(sK4(X6,X7,X8),X6) ) ),
    inference(superposition,[],[f48,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f22,f14])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f505,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl5_18
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f67,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f49,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f12,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f14])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f508,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f507])).

fof(f507,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f67,f44,f57,f440])).

fof(f440,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_enumset1(sK0,sK0,sK1))
        | r2_hidden(X3,sK2)
        | r2_hidden(X3,k1_xboole_0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f48,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_1
  <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f57,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f44,plain,(
    ! [X0,X3] : r2_hidden(X3,k1_enumset1(X0,X0,X3)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f20,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f506,plain,
    ( spl5_18
    | spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f447,f52,f61,f503])).

fof(f447,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(resolution,[],[f440,f46])).

fof(f46,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f19,f13])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f420,plain,
    ( spl5_7
    | spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f411,f369,f417,f413])).

fof(f369,plain,
    ( spl5_6
  <=> r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f411,plain,
    ( sK1 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_6 ),
    inference(resolution,[],[f371,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f18,f13])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f371,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f369])).

fof(f410,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f67,f67,f67,f285,f334])).

fof(f285,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl5_5
  <=> r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f372,plain,
    ( spl5_6
    | spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f367,f52,f283,f369])).

fof(f367,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))
    | spl5_1 ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,
    ( ! [X18] :
        ( k1_xboole_0 != X18
        | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,X18),X18)
        | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,X18),k1_enumset1(sK0,sK0,sK1)) )
    | spl5_1 ),
    inference(superposition,[],[f53,f41])).

fof(f53,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f286,plain,
    ( ~ spl5_4
    | spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f277,f52,f283,f279])).

fof(f277,plain,
    ( r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_1 ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,
    ( ! [X14] :
        ( k1_xboole_0 != X14
        | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,X14),X14)
        | ~ r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,X14),sK2) )
    | spl5_1 ),
    inference(superposition,[],[f53,f40])).

fof(f65,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f29,f61,f56,f52])).

fof(f29,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f9,f14,f13])).

fof(f9,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f64,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f28,f61,f52])).

fof(f28,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f10,f14,f13])).

fof(f10,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f59,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f27,f56,f52])).

fof(f27,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f11,f14,f13])).

fof(f11,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:34:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.13/0.51  % (16386)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.13/0.51  % (16371)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.13/0.52  % (16378)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.13/0.53  % (16368)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.30/0.53  % (16369)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (16392)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.54  % (16392)Refutation not found, incomplete strategy% (16392)------------------------------
% 1.30/0.54  % (16392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (16392)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (16392)Memory used [KB]: 1663
% 1.30/0.54  % (16392)Time elapsed: 0.125 s
% 1.30/0.54  % (16392)------------------------------
% 1.30/0.54  % (16392)------------------------------
% 1.30/0.54  % (16366)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.54  % (16376)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.54  % (16385)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.54  % (16363)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (16377)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.54  % (16377)Refutation not found, incomplete strategy% (16377)------------------------------
% 1.30/0.54  % (16377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (16377)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (16377)Memory used [KB]: 1663
% 1.30/0.54  % (16377)Time elapsed: 0.130 s
% 1.30/0.54  % (16377)------------------------------
% 1.30/0.54  % (16377)------------------------------
% 1.30/0.55  % (16367)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.30/0.55  % (16391)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.55  % (16379)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.55  % (16365)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.55  % (16379)Refutation not found, incomplete strategy% (16379)------------------------------
% 1.30/0.55  % (16379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (16379)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (16379)Memory used [KB]: 10618
% 1.30/0.55  % (16379)Time elapsed: 0.136 s
% 1.30/0.55  % (16379)------------------------------
% 1.30/0.55  % (16379)------------------------------
% 1.30/0.55  % (16381)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.56  % (16390)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.56  % (16388)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.56  % (16364)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.56  % (16372)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.57  % (16374)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.57  % (16387)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.57  % (16373)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.57  % (16384)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.57  % (16380)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.57  % (16380)Refutation not found, incomplete strategy% (16380)------------------------------
% 1.30/0.57  % (16380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (16380)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.57  
% 1.30/0.57  % (16380)Memory used [KB]: 1663
% 1.30/0.57  % (16380)Time elapsed: 0.155 s
% 1.30/0.57  % (16380)------------------------------
% 1.30/0.57  % (16380)------------------------------
% 1.30/0.57  % (16370)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.57  % (16375)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.57  % (16382)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.57  % (16383)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.58  % (16389)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.58  % (16374)Refutation not found, incomplete strategy% (16374)------------------------------
% 1.30/0.58  % (16374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.58  % (16374)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.58  
% 1.30/0.58  % (16374)Memory used [KB]: 6140
% 1.30/0.58  % (16374)Time elapsed: 0.167 s
% 1.30/0.58  % (16374)------------------------------
% 1.30/0.58  % (16374)------------------------------
% 1.30/0.60  % (16376)Refutation found. Thanks to Tanya!
% 1.30/0.60  % SZS status Theorem for theBenchmark
% 1.30/0.60  % SZS output start Proof for theBenchmark
% 1.30/0.60  fof(f716,plain,(
% 1.30/0.60    $false),
% 1.30/0.60    inference(avatar_sat_refutation,[],[f59,f64,f65,f286,f372,f410,f420,f506,f508,f565,f567,f715])).
% 1.30/0.60  fof(f715,plain,(
% 1.30/0.60    ~spl5_2 | spl5_4 | ~spl5_8),
% 1.30/0.60    inference(avatar_contradiction_clause,[],[f714])).
% 1.30/0.60  fof(f714,plain,(
% 1.30/0.60    $false | (~spl5_2 | spl5_4 | ~spl5_8)),
% 1.30/0.60    inference(subsumption_resolution,[],[f58,f705])).
% 1.30/0.60  fof(f705,plain,(
% 1.30/0.60    ~r2_hidden(sK1,sK2) | (spl5_4 | ~spl5_8)),
% 1.30/0.60    inference(superposition,[],[f281,f419])).
% 1.30/0.60  fof(f419,plain,(
% 1.30/0.60    sK1 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_8),
% 1.30/0.60    inference(avatar_component_clause,[],[f417])).
% 1.30/0.60  fof(f417,plain,(
% 1.30/0.60    spl5_8 <=> sK1 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)),
% 1.30/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.30/0.60  fof(f281,plain,(
% 1.30/0.60    ~r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | spl5_4),
% 1.30/0.60    inference(avatar_component_clause,[],[f279])).
% 1.30/0.60  fof(f279,plain,(
% 1.30/0.60    spl5_4 <=> r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 1.30/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.30/0.60  fof(f58,plain,(
% 1.30/0.60    r2_hidden(sK1,sK2) | ~spl5_2),
% 1.30/0.60    inference(avatar_component_clause,[],[f56])).
% 1.30/0.60  fof(f56,plain,(
% 1.30/0.60    spl5_2 <=> r2_hidden(sK1,sK2)),
% 1.30/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.30/0.60  fof(f567,plain,(
% 1.30/0.60    ~spl5_3 | spl5_4 | ~spl5_7),
% 1.30/0.60    inference(avatar_contradiction_clause,[],[f566])).
% 1.30/0.60  fof(f566,plain,(
% 1.30/0.60    $false | (~spl5_3 | spl5_4 | ~spl5_7)),
% 1.30/0.60    inference(subsumption_resolution,[],[f63,f426])).
% 1.30/0.60  fof(f426,plain,(
% 1.30/0.60    ~r2_hidden(sK0,sK2) | (spl5_4 | ~spl5_7)),
% 1.30/0.60    inference(superposition,[],[f281,f415])).
% 1.30/0.60  fof(f415,plain,(
% 1.30/0.60    sK0 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_7),
% 1.30/0.60    inference(avatar_component_clause,[],[f413])).
% 1.30/0.60  fof(f413,plain,(
% 1.30/0.60    spl5_7 <=> sK0 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)),
% 1.30/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.30/0.60  fof(f63,plain,(
% 1.30/0.60    r2_hidden(sK0,sK2) | ~spl5_3),
% 1.30/0.60    inference(avatar_component_clause,[],[f61])).
% 1.30/0.60  fof(f61,plain,(
% 1.30/0.60    spl5_3 <=> r2_hidden(sK0,sK2)),
% 1.30/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.30/0.60  fof(f565,plain,(
% 1.30/0.60    ~spl5_18),
% 1.30/0.60    inference(avatar_contradiction_clause,[],[f551])).
% 1.30/0.60  fof(f551,plain,(
% 1.30/0.60    $false | ~spl5_18),
% 1.30/0.60    inference(unit_resulting_resolution,[],[f67,f67,f67,f505,f334])).
% 1.30/0.60  fof(f334,plain,(
% 1.30/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK4(X2,X1,X1),X2) | ~r2_hidden(X0,X2) | r2_hidden(X0,X1) | r2_hidden(sK4(X2,X1,X1),X1)) )),
% 1.30/0.60    inference(duplicate_literal_removal,[],[f333])).
% 1.30/0.60  fof(f333,plain,(
% 1.30/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | r2_hidden(sK4(X2,X1,X1),X2) | ~r2_hidden(X0,X2) | r2_hidden(sK4(X2,X1,X1),X1)) )),
% 1.30/0.60    inference(condensation,[],[f332])).
% 1.30/0.60  fof(f332,plain,(
% 1.30/0.60    ( ! [X6,X4,X7,X5] : (r2_hidden(X4,X5) | ~r2_hidden(X4,X6) | r2_hidden(sK4(X6,X5,X5),X6) | r2_hidden(X7,X5) | ~r2_hidden(X7,X6) | r2_hidden(sK4(X6,X5,X5),X5)) )),
% 1.30/0.60    inference(duplicate_literal_removal,[],[f319])).
% 1.30/0.60  fof(f319,plain,(
% 1.30/0.60    ( ! [X6,X4,X7,X5] : (r2_hidden(X4,X5) | ~r2_hidden(X4,X6) | r2_hidden(X4,X5) | r2_hidden(sK4(X6,X5,X5),X6) | r2_hidden(X7,X5) | ~r2_hidden(X7,X6) | r2_hidden(sK4(X6,X5,X5),X5) | r2_hidden(X7,X5)) )),
% 1.30/0.60    inference(resolution,[],[f88,f77])).
% 1.30/0.60  fof(f77,plain,(
% 1.30/0.60    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK4(X2,X3,X4),X3) | r2_hidden(X5,X3) | ~r2_hidden(X5,X2) | r2_hidden(sK4(X2,X3,X4),X4) | r2_hidden(X5,X4)) )),
% 1.30/0.60    inference(superposition,[],[f48,f40])).
% 1.30/0.60  fof(f40,plain,(
% 1.30/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1)) )),
% 1.30/0.60    inference(definition_unfolding,[],[f23,f14])).
% 1.30/0.60  fof(f14,plain,(
% 1.30/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.30/0.60    inference(cnf_transformation,[],[f2])).
% 1.30/0.60  fof(f2,axiom,(
% 1.30/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.30/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.30/0.60  fof(f23,plain,(
% 1.30/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.30/0.60    inference(cnf_transformation,[],[f1])).
% 1.30/0.60  fof(f1,axiom,(
% 1.30/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.30/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.30/0.60  fof(f48,plain,(
% 1.30/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.30/0.60    inference(equality_resolution,[],[f37])).
% 1.30/0.60  fof(f37,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.30/0.60    inference(definition_unfolding,[],[f26,f14])).
% 1.30/0.60  fof(f26,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.30/0.60    inference(cnf_transformation,[],[f1])).
% 1.30/0.60  fof(f88,plain,(
% 1.30/0.60    ( ! [X6,X8,X7,X9] : (r2_hidden(sK4(X6,X7,X8),X8) | r2_hidden(X9,X7) | ~r2_hidden(X9,X6) | r2_hidden(X9,X8) | r2_hidden(sK4(X6,X7,X8),X6)) )),
% 1.30/0.60    inference(superposition,[],[f48,f41])).
% 1.30/0.60  fof(f41,plain,(
% 1.30/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0)) )),
% 1.30/0.60    inference(definition_unfolding,[],[f22,f14])).
% 1.30/0.60  fof(f22,plain,(
% 1.30/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.30/0.60    inference(cnf_transformation,[],[f1])).
% 1.30/0.60  fof(f505,plain,(
% 1.30/0.60    r2_hidden(sK0,k1_xboole_0) | ~spl5_18),
% 1.30/0.60    inference(avatar_component_clause,[],[f503])).
% 1.30/0.60  fof(f503,plain,(
% 1.30/0.60    spl5_18 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.30/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.30/0.60  fof(f67,plain,(
% 1.30/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.30/0.60    inference(condensation,[],[f66])).
% 1.30/0.60  fof(f66,plain,(
% 1.30/0.60    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 1.30/0.60    inference(superposition,[],[f49,f30])).
% 1.30/0.60  fof(f30,plain,(
% 1.30/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.30/0.60    inference(definition_unfolding,[],[f12,f14])).
% 1.30/0.60  fof(f12,plain,(
% 1.30/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.30/0.60    inference(cnf_transformation,[],[f3])).
% 1.30/0.60  fof(f3,axiom,(
% 1.30/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.30/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.30/0.60  fof(f49,plain,(
% 1.30/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.30/0.60    inference(equality_resolution,[],[f38])).
% 1.30/0.60  fof(f38,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.30/0.60    inference(definition_unfolding,[],[f25,f14])).
% 1.30/0.60  fof(f25,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.30/0.60    inference(cnf_transformation,[],[f1])).
% 1.30/0.60  fof(f508,plain,(
% 1.30/0.60    ~spl5_1 | spl5_2),
% 1.30/0.60    inference(avatar_contradiction_clause,[],[f507])).
% 1.30/0.60  fof(f507,plain,(
% 1.30/0.60    $false | (~spl5_1 | spl5_2)),
% 1.30/0.60    inference(unit_resulting_resolution,[],[f67,f44,f57,f440])).
% 1.30/0.60  fof(f440,plain,(
% 1.30/0.60    ( ! [X3] : (~r2_hidden(X3,k1_enumset1(sK0,sK0,sK1)) | r2_hidden(X3,sK2) | r2_hidden(X3,k1_xboole_0)) ) | ~spl5_1),
% 1.30/0.60    inference(superposition,[],[f48,f54])).
% 1.30/0.60  fof(f54,plain,(
% 1.30/0.60    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) | ~spl5_1),
% 1.30/0.60    inference(avatar_component_clause,[],[f52])).
% 1.30/0.60  fof(f52,plain,(
% 1.30/0.60    spl5_1 <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.30/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.30/0.60  fof(f57,plain,(
% 1.30/0.60    ~r2_hidden(sK1,sK2) | spl5_2),
% 1.30/0.60    inference(avatar_component_clause,[],[f56])).
% 1.30/0.60  fof(f44,plain,(
% 1.30/0.60    ( ! [X0,X3] : (r2_hidden(X3,k1_enumset1(X0,X0,X3))) )),
% 1.30/0.60    inference(equality_resolution,[],[f43])).
% 1.30/0.60  fof(f43,plain,(
% 1.30/0.60    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k1_enumset1(X0,X0,X3) != X2) )),
% 1.30/0.60    inference(equality_resolution,[],[f31])).
% 1.30/0.60  fof(f31,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.30/0.60    inference(definition_unfolding,[],[f20,f13])).
% 1.30/0.60  fof(f13,plain,(
% 1.30/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.30/0.60    inference(cnf_transformation,[],[f5])).
% 1.30/0.60  fof(f5,axiom,(
% 1.30/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.30/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.60  fof(f20,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.30/0.60    inference(cnf_transformation,[],[f4])).
% 1.30/0.60  fof(f4,axiom,(
% 1.30/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.30/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.30/0.60  fof(f506,plain,(
% 1.30/0.60    spl5_18 | spl5_3 | ~spl5_1),
% 1.30/0.60    inference(avatar_split_clause,[],[f447,f52,f61,f503])).
% 1.30/0.60  fof(f447,plain,(
% 1.30/0.60    r2_hidden(sK0,sK2) | r2_hidden(sK0,k1_xboole_0) | ~spl5_1),
% 1.30/0.60    inference(resolution,[],[f440,f46])).
% 1.30/0.60  fof(f46,plain,(
% 1.30/0.60    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 1.30/0.60    inference(equality_resolution,[],[f45])).
% 1.30/0.60  fof(f45,plain,(
% 1.30/0.60    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 1.30/0.60    inference(equality_resolution,[],[f32])).
% 1.30/0.60  fof(f32,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.30/0.60    inference(definition_unfolding,[],[f19,f13])).
% 1.30/0.60  fof(f19,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.30/0.60    inference(cnf_transformation,[],[f4])).
% 1.30/0.60  fof(f420,plain,(
% 1.30/0.60    spl5_7 | spl5_8 | ~spl5_6),
% 1.30/0.60    inference(avatar_split_clause,[],[f411,f369,f417,f413])).
% 1.30/0.60  fof(f369,plain,(
% 1.30/0.60    spl5_6 <=> r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))),
% 1.30/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.30/0.60  fof(f411,plain,(
% 1.30/0.60    sK1 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 = sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_6),
% 1.30/0.60    inference(resolution,[],[f371,f47])).
% 1.30/0.60  fof(f47,plain,(
% 1.30/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.30/0.60    inference(equality_resolution,[],[f33])).
% 1.30/0.60  fof(f33,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.30/0.60    inference(definition_unfolding,[],[f18,f13])).
% 1.30/0.60  fof(f18,plain,(
% 1.30/0.60    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.30/0.60    inference(cnf_transformation,[],[f4])).
% 1.30/0.60  fof(f371,plain,(
% 1.30/0.60    r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) | ~spl5_6),
% 1.30/0.60    inference(avatar_component_clause,[],[f369])).
% 1.30/0.60  fof(f410,plain,(
% 1.30/0.60    ~spl5_5),
% 1.30/0.60    inference(avatar_contradiction_clause,[],[f390])).
% 1.30/0.60  fof(f390,plain,(
% 1.30/0.60    $false | ~spl5_5),
% 1.30/0.60    inference(unit_resulting_resolution,[],[f67,f67,f67,f285,f334])).
% 1.30/0.60  fof(f285,plain,(
% 1.30/0.60    r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~spl5_5),
% 1.30/0.60    inference(avatar_component_clause,[],[f283])).
% 1.30/0.60  fof(f283,plain,(
% 1.30/0.60    spl5_5 <=> r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)),
% 1.30/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.30/0.60  fof(f372,plain,(
% 1.30/0.60    spl5_6 | spl5_5 | spl5_1),
% 1.30/0.60    inference(avatar_split_clause,[],[f367,f52,f283,f369])).
% 1.30/0.60  fof(f367,plain,(
% 1.30/0.60    r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) | spl5_1),
% 1.30/0.60    inference(equality_resolution,[],[f91])).
% 1.30/0.60  fof(f91,plain,(
% 1.30/0.60    ( ! [X18] : (k1_xboole_0 != X18 | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,X18),X18) | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,X18),k1_enumset1(sK0,sK0,sK1))) ) | spl5_1),
% 1.30/0.60    inference(superposition,[],[f53,f41])).
% 1.30/0.60  fof(f53,plain,(
% 1.30/0.60    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) | spl5_1),
% 1.30/0.60    inference(avatar_component_clause,[],[f52])).
% 1.30/0.60  fof(f286,plain,(
% 1.30/0.60    ~spl5_4 | spl5_5 | spl5_1),
% 1.30/0.60    inference(avatar_split_clause,[],[f277,f52,f283,f279])).
% 1.30/0.60  fof(f277,plain,(
% 1.30/0.60    r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | spl5_1),
% 1.30/0.60    inference(equality_resolution,[],[f80])).
% 1.30/0.60  fof(f80,plain,(
% 1.30/0.60    ( ! [X14] : (k1_xboole_0 != X14 | r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,X14),X14) | ~r2_hidden(sK4(k1_enumset1(sK0,sK0,sK1),sK2,X14),sK2)) ) | spl5_1),
% 1.30/0.60    inference(superposition,[],[f53,f40])).
% 1.30/0.60  fof(f65,plain,(
% 1.30/0.60    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.30/0.60    inference(avatar_split_clause,[],[f29,f61,f56,f52])).
% 1.30/0.60  fof(f29,plain,(
% 1.30/0.60    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.30/0.60    inference(definition_unfolding,[],[f9,f14,f13])).
% 1.30/0.60  fof(f9,plain,(
% 1.30/0.60    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.30/0.60    inference(cnf_transformation,[],[f8])).
% 1.30/0.60  fof(f8,plain,(
% 1.30/0.60    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.30/0.60    inference(ennf_transformation,[],[f7])).
% 1.30/0.60  fof(f7,negated_conjecture,(
% 1.30/0.60    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.30/0.60    inference(negated_conjecture,[],[f6])).
% 1.30/0.60  fof(f6,conjecture,(
% 1.30/0.60    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.30/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.30/0.60  fof(f64,plain,(
% 1.30/0.60    spl5_1 | spl5_3),
% 1.30/0.60    inference(avatar_split_clause,[],[f28,f61,f52])).
% 1.30/0.60  fof(f28,plain,(
% 1.30/0.60    r2_hidden(sK0,sK2) | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.30/0.60    inference(definition_unfolding,[],[f10,f14,f13])).
% 1.30/0.60  fof(f10,plain,(
% 1.30/0.60    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.30/0.60    inference(cnf_transformation,[],[f8])).
% 1.30/0.60  fof(f59,plain,(
% 1.30/0.60    spl5_1 | spl5_2),
% 1.30/0.60    inference(avatar_split_clause,[],[f27,f56,f52])).
% 1.30/0.60  fof(f27,plain,(
% 1.30/0.60    r2_hidden(sK1,sK2) | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.30/0.60    inference(definition_unfolding,[],[f11,f14,f13])).
% 1.30/0.60  fof(f11,plain,(
% 1.30/0.60    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.30/0.60    inference(cnf_transformation,[],[f8])).
% 1.30/0.60  % SZS output end Proof for theBenchmark
% 1.30/0.60  % (16376)------------------------------
% 1.30/0.60  % (16376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.60  % (16376)Termination reason: Refutation
% 1.30/0.60  
% 1.30/0.60  % (16376)Memory used [KB]: 6652
% 1.30/0.60  % (16376)Time elapsed: 0.162 s
% 1.30/0.60  % (16376)------------------------------
% 1.30/0.60  % (16376)------------------------------
% 1.30/0.60  % (16362)Success in time 0.231 s
%------------------------------------------------------------------------------
