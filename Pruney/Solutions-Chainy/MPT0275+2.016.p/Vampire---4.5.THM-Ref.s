%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:28 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
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
fof(f937,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f72,f385,f533,f579,f590,f698,f701,f774,f776,f936])).

fof(f936,plain,
    ( ~ spl5_2
    | spl5_4
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f935])).

fof(f935,plain,
    ( $false
    | ~ spl5_2
    | spl5_4
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f65,f926])).

fof(f926,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f380,f589])).

fof(f589,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f587])).

fof(f587,plain,
    ( spl5_8
  <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f380,plain,
    ( ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl5_4
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f65,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f776,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f775])).

fof(f775,plain,
    ( $false
    | ~ spl5_3
    | spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f70,f596])).

fof(f596,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl5_4
    | ~ spl5_7 ),
    inference(superposition,[],[f380,f585])).

fof(f585,plain,
    ( sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f583])).

fof(f583,plain,
    ( spl5_7
  <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f70,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f774,plain,(
    ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f74,f74,f74,f697,f433])).

fof(f433,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X2,X1,X1),X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | r2_hidden(sK3(X2,X1,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f432])).

fof(f432,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(sK3(X2,X1,X1),X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(sK3(X2,X1,X1),X1) ) ),
    inference(condensation,[],[f431])).

fof(f431,plain,(
    ! [X4,X2,X5,X3] :
      ( r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X4)
      | r2_hidden(sK3(X4,X3,X3),X4)
      | r2_hidden(X5,X3)
      | ~ r2_hidden(X5,X4)
      | r2_hidden(sK3(X4,X3,X3),X3) ) ),
    inference(duplicate_literal_removal,[],[f415])).

fof(f415,plain,(
    ! [X4,X2,X5,X3] :
      ( r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X4)
      | r2_hidden(X2,X3)
      | r2_hidden(sK3(X4,X3,X3),X4)
      | r2_hidden(X5,X3)
      | ~ r2_hidden(X5,X4)
      | r2_hidden(sK3(X4,X3,X3),X3)
      | r2_hidden(X5,X3) ) ),
    inference(resolution,[],[f95,f84])).

fof(f84,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK3(X2,X3,X4),X3)
      | r2_hidden(X5,X3)
      | ~ r2_hidden(X5,X2)
      | r2_hidden(sK3(X2,X3,X4),X4)
      | r2_hidden(X5,X4) ) ),
    inference(superposition,[],[f50,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1) ) ),
    inference(definition_unfolding,[],[f18,f15])).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f21,f15])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f95,plain,(
    ! [X6,X8,X7,X9] :
      ( r2_hidden(sK3(X6,X7,X8),X8)
      | r2_hidden(X9,X7)
      | ~ r2_hidden(X9,X6)
      | r2_hidden(X9,X8)
      | r2_hidden(sK3(X6,X7,X8),X6) ) ),
    inference(superposition,[],[f50,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f17,f15])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f697,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f695])).

fof(f695,plain,
    ( spl5_20
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f74,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f51,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f13,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f20,f15])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f701,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f700])).

fof(f700,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f74,f54,f64,f614])).

fof(f614,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_enumset1(sK0,sK0,sK1))
        | r2_hidden(X3,sK2)
        | r2_hidden(X3,k1_xboole_0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f50,f61])).

fof(f61,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_1
  <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f64,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f54,plain,(
    ! [X0,X3] : r2_hidden(X3,k1_enumset1(X0,X0,X3)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f27,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f698,plain,
    ( spl5_20
    | spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f628,f59,f68,f695])).

fof(f628,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(resolution,[],[f614,f56])).

fof(f56,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f26,f14])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f590,plain,
    ( spl5_7
    | spl5_8
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f581,f530,f587,f583])).

fof(f530,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f581,plain,
    ( sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)
    | ~ spl5_6 ),
    inference(resolution,[],[f532,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f25,f14])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f532,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f530])).

fof(f579,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f74,f74,f74,f384,f433])).

fof(f384,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl5_5
  <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f533,plain,
    ( spl5_6
    | spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f528,f59,f382,f530])).

fof(f528,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))
    | spl5_1 ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,
    ( ! [X18] :
        ( k1_xboole_0 != X18
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X18),X18)
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X18),k1_enumset1(sK0,sK0,sK1)) )
    | spl5_1 ),
    inference(superposition,[],[f60,f39])).

fof(f60,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f385,plain,
    ( ~ spl5_4
    | spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f376,f59,f382,f378])).

fof(f376,plain,
    ( r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)
    | spl5_1 ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,
    ( ! [X14] :
        ( k1_xboole_0 != X14
        | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X14),X14)
        | ~ r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X14),sK2) )
    | spl5_1 ),
    inference(superposition,[],[f60,f38])).

fof(f72,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f33,f68,f63,f59])).

fof(f33,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f10,f15,f14])).

fof(f10,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

fof(f71,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f32,f68,f59])).

fof(f32,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f11,f15,f14])).

fof(f11,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f31,f63,f59])).

fof(f31,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f12,f15,f14])).

fof(f12,plain,
    ( r2_hidden(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:46:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (14930)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (14937)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (14937)Refutation not found, incomplete strategy% (14937)------------------------------
% 0.21/0.52  % (14937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14931)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (14937)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14937)Memory used [KB]: 6140
% 0.21/0.53  % (14937)Time elapsed: 0.109 s
% 0.21/0.53  % (14937)------------------------------
% 0.21/0.53  % (14937)------------------------------
% 0.21/0.54  % (14945)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (14936)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (14927)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (14928)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (14955)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (14926)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.54  % (14938)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.55  % (14940)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.55  % (14948)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.55  % (14947)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.55  % (14941)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.55  % (14929)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.56  % (14953)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.56  % (14950)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.56  % (14939)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.56  % (14940)Refutation not found, incomplete strategy% (14940)------------------------------
% 1.34/0.56  % (14940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (14940)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (14940)Memory used [KB]: 1663
% 1.34/0.56  % (14940)Time elapsed: 0.098 s
% 1.34/0.56  % (14940)------------------------------
% 1.34/0.56  % (14940)------------------------------
% 1.34/0.56  % (14951)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.56  % (14955)Refutation not found, incomplete strategy% (14955)------------------------------
% 1.34/0.56  % (14955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (14955)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (14955)Memory used [KB]: 1663
% 1.34/0.56  % (14955)Time elapsed: 0.117 s
% 1.34/0.56  % (14955)------------------------------
% 1.34/0.56  % (14955)------------------------------
% 1.34/0.56  % (14949)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.59/0.57  % (14942)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.59/0.57  % (14954)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.59/0.57  % (14933)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.59/0.57  % (14942)Refutation not found, incomplete strategy% (14942)------------------------------
% 1.59/0.57  % (14942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (14942)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (14942)Memory used [KB]: 10618
% 1.59/0.57  % (14942)Time elapsed: 0.156 s
% 1.59/0.57  % (14942)------------------------------
% 1.59/0.57  % (14942)------------------------------
% 1.59/0.57  % (14935)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.59/0.57  % (14952)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.59/0.57  % (14932)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.57  % (14944)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.59/0.57  % (14946)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.59/0.58  % (14943)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.59/0.58  % (14934)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.59/0.58  % (14943)Refutation not found, incomplete strategy% (14943)------------------------------
% 1.59/0.58  % (14943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (14943)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (14943)Memory used [KB]: 1791
% 1.59/0.58  % (14943)Time elapsed: 0.167 s
% 1.59/0.58  % (14943)------------------------------
% 1.59/0.58  % (14943)------------------------------
% 1.59/0.61  % (14939)Refutation found. Thanks to Tanya!
% 1.59/0.61  % SZS status Theorem for theBenchmark
% 1.59/0.62  % SZS output start Proof for theBenchmark
% 1.59/0.62  fof(f937,plain,(
% 1.59/0.62    $false),
% 1.59/0.62    inference(avatar_sat_refutation,[],[f66,f71,f72,f385,f533,f579,f590,f698,f701,f774,f776,f936])).
% 1.59/0.63  fof(f936,plain,(
% 1.59/0.63    ~spl5_2 | spl5_4 | ~spl5_8),
% 1.59/0.63    inference(avatar_contradiction_clause,[],[f935])).
% 1.59/0.63  fof(f935,plain,(
% 1.59/0.63    $false | (~spl5_2 | spl5_4 | ~spl5_8)),
% 1.59/0.63    inference(subsumption_resolution,[],[f65,f926])).
% 1.59/0.63  fof(f926,plain,(
% 1.59/0.63    ~r2_hidden(sK1,sK2) | (spl5_4 | ~spl5_8)),
% 1.59/0.63    inference(superposition,[],[f380,f589])).
% 1.59/0.63  fof(f589,plain,(
% 1.59/0.63    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_8),
% 1.59/0.63    inference(avatar_component_clause,[],[f587])).
% 1.59/0.63  fof(f587,plain,(
% 1.59/0.63    spl5_8 <=> sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.59/0.63  fof(f380,plain,(
% 1.59/0.63    ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | spl5_4),
% 1.59/0.63    inference(avatar_component_clause,[],[f378])).
% 1.59/0.63  fof(f378,plain,(
% 1.59/0.63    spl5_4 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.59/0.63  fof(f65,plain,(
% 1.59/0.63    r2_hidden(sK1,sK2) | ~spl5_2),
% 1.59/0.63    inference(avatar_component_clause,[],[f63])).
% 1.59/0.63  fof(f63,plain,(
% 1.59/0.63    spl5_2 <=> r2_hidden(sK1,sK2)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.59/0.63  fof(f776,plain,(
% 1.59/0.63    ~spl5_3 | spl5_4 | ~spl5_7),
% 1.59/0.63    inference(avatar_contradiction_clause,[],[f775])).
% 1.59/0.63  fof(f775,plain,(
% 1.59/0.63    $false | (~spl5_3 | spl5_4 | ~spl5_7)),
% 1.59/0.63    inference(subsumption_resolution,[],[f70,f596])).
% 1.59/0.63  fof(f596,plain,(
% 1.59/0.63    ~r2_hidden(sK0,sK2) | (spl5_4 | ~spl5_7)),
% 1.59/0.63    inference(superposition,[],[f380,f585])).
% 1.59/0.63  fof(f585,plain,(
% 1.59/0.63    sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_7),
% 1.59/0.63    inference(avatar_component_clause,[],[f583])).
% 1.59/0.63  fof(f583,plain,(
% 1.59/0.63    spl5_7 <=> sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.59/0.63  fof(f70,plain,(
% 1.59/0.63    r2_hidden(sK0,sK2) | ~spl5_3),
% 1.59/0.63    inference(avatar_component_clause,[],[f68])).
% 1.59/0.63  fof(f68,plain,(
% 1.59/0.63    spl5_3 <=> r2_hidden(sK0,sK2)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.59/0.63  fof(f774,plain,(
% 1.59/0.63    ~spl5_20),
% 1.59/0.63    inference(avatar_contradiction_clause,[],[f756])).
% 1.59/0.63  fof(f756,plain,(
% 1.59/0.63    $false | ~spl5_20),
% 1.59/0.63    inference(unit_resulting_resolution,[],[f74,f74,f74,f697,f433])).
% 1.59/0.63  fof(f433,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK3(X2,X1,X1),X2) | ~r2_hidden(X0,X2) | r2_hidden(X0,X1) | r2_hidden(sK3(X2,X1,X1),X1)) )),
% 1.59/0.63    inference(duplicate_literal_removal,[],[f432])).
% 1.59/0.63  fof(f432,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | r2_hidden(sK3(X2,X1,X1),X2) | ~r2_hidden(X0,X2) | r2_hidden(sK3(X2,X1,X1),X1)) )),
% 1.59/0.63    inference(condensation,[],[f431])).
% 1.59/0.63  fof(f431,plain,(
% 1.59/0.63    ( ! [X4,X2,X5,X3] : (r2_hidden(X2,X3) | ~r2_hidden(X2,X4) | r2_hidden(sK3(X4,X3,X3),X4) | r2_hidden(X5,X3) | ~r2_hidden(X5,X4) | r2_hidden(sK3(X4,X3,X3),X3)) )),
% 1.59/0.63    inference(duplicate_literal_removal,[],[f415])).
% 1.59/0.63  fof(f415,plain,(
% 1.59/0.63    ( ! [X4,X2,X5,X3] : (r2_hidden(X2,X3) | ~r2_hidden(X2,X4) | r2_hidden(X2,X3) | r2_hidden(sK3(X4,X3,X3),X4) | r2_hidden(X5,X3) | ~r2_hidden(X5,X4) | r2_hidden(sK3(X4,X3,X3),X3) | r2_hidden(X5,X3)) )),
% 1.59/0.63    inference(resolution,[],[f95,f84])).
% 1.59/0.63  fof(f84,plain,(
% 1.59/0.63    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK3(X2,X3,X4),X3) | r2_hidden(X5,X3) | ~r2_hidden(X5,X2) | r2_hidden(sK3(X2,X3,X4),X4) | r2_hidden(X5,X4)) )),
% 1.59/0.63    inference(superposition,[],[f50,f38])).
% 1.59/0.63  fof(f38,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1)) )),
% 1.59/0.63    inference(definition_unfolding,[],[f18,f15])).
% 1.59/0.63  fof(f15,plain,(
% 1.59/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.59/0.63    inference(cnf_transformation,[],[f2])).
% 1.59/0.63  fof(f2,axiom,(
% 1.59/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.59/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.59/0.63  fof(f18,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.59/0.63    inference(cnf_transformation,[],[f1])).
% 1.59/0.63  fof(f1,axiom,(
% 1.59/0.63    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.59/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.59/0.63  fof(f50,plain,(
% 1.59/0.63    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.59/0.63    inference(equality_resolution,[],[f35])).
% 1.59/0.63  fof(f35,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.59/0.63    inference(definition_unfolding,[],[f21,f15])).
% 1.59/0.63  fof(f21,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.59/0.63    inference(cnf_transformation,[],[f1])).
% 1.59/0.63  fof(f95,plain,(
% 1.59/0.63    ( ! [X6,X8,X7,X9] : (r2_hidden(sK3(X6,X7,X8),X8) | r2_hidden(X9,X7) | ~r2_hidden(X9,X6) | r2_hidden(X9,X8) | r2_hidden(sK3(X6,X7,X8),X6)) )),
% 1.59/0.63    inference(superposition,[],[f50,f39])).
% 1.59/0.63  fof(f39,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0)) )),
% 1.59/0.63    inference(definition_unfolding,[],[f17,f15])).
% 1.59/0.63  fof(f17,plain,(
% 1.59/0.63    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 1.59/0.63    inference(cnf_transformation,[],[f1])).
% 1.59/0.63  fof(f697,plain,(
% 1.59/0.63    r2_hidden(sK0,k1_xboole_0) | ~spl5_20),
% 1.59/0.63    inference(avatar_component_clause,[],[f695])).
% 1.59/0.63  fof(f695,plain,(
% 1.59/0.63    spl5_20 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.59/0.63  fof(f74,plain,(
% 1.59/0.63    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.59/0.63    inference(condensation,[],[f73])).
% 1.59/0.63  fof(f73,plain,(
% 1.59/0.63    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.59/0.63    inference(superposition,[],[f51,f34])).
% 1.59/0.63  fof(f34,plain,(
% 1.59/0.63    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.59/0.63    inference(definition_unfolding,[],[f13,f15])).
% 1.59/0.63  fof(f13,plain,(
% 1.59/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.59/0.63    inference(cnf_transformation,[],[f3])).
% 1.59/0.63  fof(f3,axiom,(
% 1.59/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.59/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.59/0.63  fof(f51,plain,(
% 1.59/0.63    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.59/0.63    inference(equality_resolution,[],[f36])).
% 1.59/0.63  fof(f36,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.59/0.63    inference(definition_unfolding,[],[f20,f15])).
% 1.59/0.63  fof(f20,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.59/0.63    inference(cnf_transformation,[],[f1])).
% 1.59/0.63  fof(f701,plain,(
% 1.59/0.63    ~spl5_1 | spl5_2),
% 1.59/0.63    inference(avatar_contradiction_clause,[],[f700])).
% 1.59/0.63  fof(f700,plain,(
% 1.59/0.63    $false | (~spl5_1 | spl5_2)),
% 1.59/0.63    inference(unit_resulting_resolution,[],[f74,f54,f64,f614])).
% 1.59/0.63  fof(f614,plain,(
% 1.59/0.63    ( ! [X3] : (~r2_hidden(X3,k1_enumset1(sK0,sK0,sK1)) | r2_hidden(X3,sK2) | r2_hidden(X3,k1_xboole_0)) ) | ~spl5_1),
% 1.59/0.63    inference(superposition,[],[f50,f61])).
% 1.59/0.63  fof(f61,plain,(
% 1.59/0.63    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) | ~spl5_1),
% 1.59/0.63    inference(avatar_component_clause,[],[f59])).
% 1.59/0.63  fof(f59,plain,(
% 1.59/0.63    spl5_1 <=> k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.59/0.63  fof(f64,plain,(
% 1.59/0.63    ~r2_hidden(sK1,sK2) | spl5_2),
% 1.59/0.63    inference(avatar_component_clause,[],[f63])).
% 1.59/0.63  fof(f54,plain,(
% 1.59/0.63    ( ! [X0,X3] : (r2_hidden(X3,k1_enumset1(X0,X0,X3))) )),
% 1.59/0.63    inference(equality_resolution,[],[f53])).
% 1.59/0.63  fof(f53,plain,(
% 1.59/0.63    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k1_enumset1(X0,X0,X3) != X2) )),
% 1.59/0.63    inference(equality_resolution,[],[f41])).
% 1.59/0.63  fof(f41,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.59/0.63    inference(definition_unfolding,[],[f27,f14])).
% 1.59/0.63  fof(f14,plain,(
% 1.59/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.59/0.63    inference(cnf_transformation,[],[f5])).
% 1.59/0.63  fof(f5,axiom,(
% 1.59/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.59/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.63  fof(f27,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.59/0.63    inference(cnf_transformation,[],[f4])).
% 1.59/0.63  fof(f4,axiom,(
% 1.59/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.59/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.59/0.63  fof(f698,plain,(
% 1.59/0.63    spl5_20 | spl5_3 | ~spl5_1),
% 1.59/0.63    inference(avatar_split_clause,[],[f628,f59,f68,f695])).
% 1.59/0.63  fof(f628,plain,(
% 1.59/0.63    r2_hidden(sK0,sK2) | r2_hidden(sK0,k1_xboole_0) | ~spl5_1),
% 1.59/0.63    inference(resolution,[],[f614,f56])).
% 1.59/0.63  fof(f56,plain,(
% 1.59/0.63    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 1.59/0.63    inference(equality_resolution,[],[f55])).
% 1.59/0.63  fof(f55,plain,(
% 1.59/0.63    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 1.59/0.63    inference(equality_resolution,[],[f42])).
% 1.59/0.63  fof(f42,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.59/0.63    inference(definition_unfolding,[],[f26,f14])).
% 1.59/0.63  fof(f26,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.59/0.63    inference(cnf_transformation,[],[f4])).
% 1.59/0.63  fof(f590,plain,(
% 1.59/0.63    spl5_7 | spl5_8 | ~spl5_6),
% 1.59/0.63    inference(avatar_split_clause,[],[f581,f530,f587,f583])).
% 1.59/0.63  fof(f530,plain,(
% 1.59/0.63    spl5_6 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1))),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.59/0.63  fof(f581,plain,(
% 1.59/0.63    sK1 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | sK0 = sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0) | ~spl5_6),
% 1.59/0.63    inference(resolution,[],[f532,f57])).
% 1.59/0.63  fof(f57,plain,(
% 1.59/0.63    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_enumset1(X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.59/0.63    inference(equality_resolution,[],[f43])).
% 1.59/0.63  fof(f43,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.59/0.63    inference(definition_unfolding,[],[f25,f14])).
% 1.59/0.63  fof(f25,plain,(
% 1.59/0.63    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.59/0.63    inference(cnf_transformation,[],[f4])).
% 1.59/0.63  fof(f532,plain,(
% 1.59/0.63    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) | ~spl5_6),
% 1.59/0.63    inference(avatar_component_clause,[],[f530])).
% 1.59/0.63  fof(f579,plain,(
% 1.59/0.63    ~spl5_5),
% 1.59/0.63    inference(avatar_contradiction_clause,[],[f555])).
% 1.59/0.63  fof(f555,plain,(
% 1.59/0.63    $false | ~spl5_5),
% 1.59/0.63    inference(unit_resulting_resolution,[],[f74,f74,f74,f384,f433])).
% 1.59/0.63  fof(f384,plain,(
% 1.59/0.63    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~spl5_5),
% 1.59/0.63    inference(avatar_component_clause,[],[f382])).
% 1.59/0.63  fof(f382,plain,(
% 1.59/0.63    spl5_5 <=> r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0)),
% 1.59/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.59/0.63  fof(f533,plain,(
% 1.59/0.63    spl5_6 | spl5_5 | spl5_1),
% 1.59/0.63    inference(avatar_split_clause,[],[f528,f59,f382,f530])).
% 1.59/0.63  fof(f528,plain,(
% 1.59/0.63    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_enumset1(sK0,sK0,sK1)) | spl5_1),
% 1.59/0.63    inference(equality_resolution,[],[f98])).
% 1.59/0.63  fof(f98,plain,(
% 1.59/0.63    ( ! [X18] : (k1_xboole_0 != X18 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X18),X18) | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X18),k1_enumset1(sK0,sK0,sK1))) ) | spl5_1),
% 1.59/0.63    inference(superposition,[],[f60,f39])).
% 1.59/0.63  fof(f60,plain,(
% 1.59/0.63    k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)) | spl5_1),
% 1.59/0.63    inference(avatar_component_clause,[],[f59])).
% 1.59/0.63  fof(f385,plain,(
% 1.59/0.63    ~spl5_4 | spl5_5 | spl5_1),
% 1.59/0.63    inference(avatar_split_clause,[],[f376,f59,f382,f378])).
% 1.59/0.63  fof(f376,plain,(
% 1.59/0.63    r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),k1_xboole_0) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,k1_xboole_0),sK2) | spl5_1),
% 1.59/0.63    inference(equality_resolution,[],[f87])).
% 1.59/0.63  fof(f87,plain,(
% 1.59/0.63    ( ! [X14] : (k1_xboole_0 != X14 | r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X14),X14) | ~r2_hidden(sK3(k1_enumset1(sK0,sK0,sK1),sK2,X14),sK2)) ) | spl5_1),
% 1.59/0.63    inference(superposition,[],[f60,f38])).
% 1.59/0.63  fof(f72,plain,(
% 1.59/0.63    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.59/0.63    inference(avatar_split_clause,[],[f33,f68,f63,f59])).
% 1.59/0.63  fof(f33,plain,(
% 1.59/0.63    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.59/0.63    inference(definition_unfolding,[],[f10,f15,f14])).
% 1.59/0.63  fof(f10,plain,(
% 1.59/0.63    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK2) | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.59/0.63    inference(cnf_transformation,[],[f9])).
% 1.59/0.63  fof(f9,plain,(
% 1.59/0.63    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.59/0.63    inference(ennf_transformation,[],[f8])).
% 1.59/0.63  fof(f8,negated_conjecture,(
% 1.59/0.63    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.59/0.63    inference(negated_conjecture,[],[f7])).
% 1.59/0.63  fof(f7,conjecture,(
% 1.59/0.63    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.59/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).
% 1.59/0.63  fof(f71,plain,(
% 1.59/0.63    spl5_1 | spl5_3),
% 1.59/0.63    inference(avatar_split_clause,[],[f32,f68,f59])).
% 1.59/0.63  fof(f32,plain,(
% 1.59/0.63    r2_hidden(sK0,sK2) | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.59/0.63    inference(definition_unfolding,[],[f11,f15,f14])).
% 1.59/0.63  fof(f11,plain,(
% 1.59/0.63    r2_hidden(sK0,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.59/0.63    inference(cnf_transformation,[],[f9])).
% 1.59/0.63  fof(f66,plain,(
% 1.59/0.63    spl5_1 | spl5_2),
% 1.59/0.63    inference(avatar_split_clause,[],[f31,f63,f59])).
% 1.59/0.63  fof(f31,plain,(
% 1.59/0.63    r2_hidden(sK1,sK2) | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k3_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2))),
% 1.59/0.63    inference(definition_unfolding,[],[f12,f15,f14])).
% 1.59/0.63  fof(f12,plain,(
% 1.59/0.63    r2_hidden(sK1,sK2) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.59/0.63    inference(cnf_transformation,[],[f9])).
% 1.59/0.63  % SZS output end Proof for theBenchmark
% 1.59/0.63  % (14939)------------------------------
% 1.59/0.63  % (14939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.63  % (14939)Termination reason: Refutation
% 1.59/0.63  
% 1.59/0.63  % (14939)Memory used [KB]: 6780
% 1.59/0.63  % (14939)Time elapsed: 0.187 s
% 1.59/0.63  % (14939)------------------------------
% 1.59/0.63  % (14939)------------------------------
% 1.59/0.63  % (14917)Success in time 0.264 s
%------------------------------------------------------------------------------
