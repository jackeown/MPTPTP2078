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
% DateTime   : Thu Dec  3 12:37:21 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 495 expanded)
%              Number of leaves         :   38 ( 168 expanded)
%              Depth                    :   14
%              Number of atoms          :  448 (1229 expanded)
%              Number of equality atoms :  163 ( 473 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1004,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f94,f332,f346,f443,f461,f544,f599,f607,f620,f639,f651,f673,f756,f770,f792,f802,f874,f875,f953,f964,f972,f1003])).

fof(f1003,plain,
    ( spl4_31
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(avatar_contradiction_clause,[],[f999])).

fof(f999,plain,
    ( $false
    | spl4_31
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(unit_resulting_resolution,[],[f594,f66,f998])).

fof(f998,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tarski(X1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X1 )
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(duplicate_literal_removal,[],[f997])).

fof(f997,plain,
    ( ! [X1] :
        ( sK1 = X1
        | ~ r1_tarski(k1_tarski(X1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X1 )
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f956,f971])).

fof(f971,plain,
    ( sK1 = sK2
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f969])).

fof(f969,plain,
    ( spl4_52
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f956,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tarski(X1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK2 = X1
        | sK1 = X1 )
    | ~ spl4_50 ),
    inference(superposition,[],[f59,f952])).

fof(f952,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f950])).

fof(f950,plain,
    ( spl4_50
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f34,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f594,plain,
    ( sK0 != sK1
    | spl4_31 ),
    inference(avatar_component_clause,[],[f593])).

fof(f593,plain,
    ( spl4_31
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f972,plain,
    ( spl4_52
    | spl4_1
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f965,f961,f75,f969])).

fof(f75,plain,
    ( spl4_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f961,plain,
    ( spl4_51
  <=> r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f965,plain,
    ( sK0 = sK2
    | sK1 = sK2
    | ~ spl4_51 ),
    inference(resolution,[],[f963,f59])).

fof(f963,plain,
    ( r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f961])).

fof(f964,plain,
    ( spl4_51
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f959,f950,f961])).

fof(f959,plain,
    ( r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_50 ),
    inference(superposition,[],[f66,f952])).

fof(f953,plain,
    ( spl4_50
    | ~ spl4_10
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f941,f604,f386,f950])).

fof(f386,plain,
    ( spl4_10
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f604,plain,
    ( spl4_33
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f941,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)
    | ~ spl4_10
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f388,f606])).

fof(f606,plain,
    ( sK1 = sK3
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f604])).

fof(f388,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f386])).

fof(f875,plain,
    ( sK0 != sK1
    | sK1 != sK3
    | sK0 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f874,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f869])).

fof(f869,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_39 ),
    inference(unit_resulting_resolution,[],[f77,f391,f825])).

fof(f825,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X1))
        | sK0 = X1 )
    | ~ spl4_39 ),
    inference(superposition,[],[f48,f742])).

fof(f742,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f741])).

fof(f741,plain,
    ( spl4_39
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f391,plain,
    ( ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(resolution,[],[f328,f152])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f138,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f138,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f137,f87])).

fof(f87,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_3
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_tarski(X0,X1) ) ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f44,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f111,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f51,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f56,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f111,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(X3,k4_xboole_0(X3,X4))
      | k1_xboole_0 = k4_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f107,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f328,plain,
    ( ! [X2,X1] : r1_tarski(k3_xboole_0(k1_xboole_0,X1),X2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl4_7
  <=> ! [X1,X2] : r1_tarski(k3_xboole_0(k1_xboole_0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f77,plain,
    ( sK0 != sK2
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f802,plain,
    ( ~ spl4_3
    | ~ spl4_15
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f797])).

fof(f797,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_15
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f138,f743,f460,f38])).

fof(f460,plain,
    ( r1_tarski(k1_tarski(sK0),k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl4_15
  <=> r1_tarski(k1_tarski(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f743,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl4_39 ),
    inference(avatar_component_clause,[],[f741])).

fof(f792,plain,(
    ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f780])).

fof(f780,plain,
    ( $false
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f67,f67,f619,f38])).

fof(f619,plain,
    ( ! [X2] : k1_tarski(X2) != k1_tarski(sK2)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f618])).

fof(f618,plain,
    ( spl4_34
  <=> ! [X2] : k1_tarski(X2) != k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f770,plain,
    ( spl4_1
    | ~ spl4_41 ),
    inference(avatar_contradiction_clause,[],[f766])).

fof(f766,plain,
    ( $false
    | spl4_1
    | ~ spl4_41 ),
    inference(unit_resulting_resolution,[],[f77,f67,f764])).

fof(f764,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tarski(X1),k1_tarski(sK2))
        | sK0 = X1 )
    | ~ spl4_41 ),
    inference(duplicate_literal_removal,[],[f760])).

fof(f760,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tarski(X1),k1_tarski(sK2))
        | sK0 = X1
        | sK0 = X1 )
    | ~ spl4_41 ),
    inference(superposition,[],[f59,f755])).

fof(f755,plain,
    ( k1_tarski(sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f753])).

fof(f753,plain,
    ( spl4_41
  <=> k1_tarski(sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f756,plain,
    ( spl4_41
    | ~ spl4_12
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f739,f593,f436,f753])).

fof(f436,plain,
    ( spl4_12
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f739,plain,
    ( k1_tarski(sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_12
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f438,f595])).

fof(f595,plain,
    ( sK0 = sK1
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f593])).

fof(f438,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f436])).

fof(f673,plain,(
    ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f661])).

fof(f661,plain,
    ( $false
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f67,f67,f598,f38])).

fof(f598,plain,
    ( ! [X2] : k1_tarski(X2) != k1_tarski(sK3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl4_32
  <=> ! [X2] : k1_tarski(X2) != k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f651,plain,
    ( spl4_2
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f647])).

fof(f647,plain,
    ( $false
    | spl4_2
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f82,f67,f645])).

fof(f645,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tarski(X1),k1_tarski(sK3))
        | sK0 = X1 )
    | ~ spl4_36 ),
    inference(duplicate_literal_removal,[],[f641])).

fof(f641,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_tarski(X1),k1_tarski(sK3))
        | sK0 = X1
        | sK0 = X1 )
    | ~ spl4_36 ),
    inference(superposition,[],[f59,f638])).

fof(f638,plain,
    ( k1_tarski(sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f636])).

fof(f636,plain,
    ( spl4_36
  <=> k1_tarski(sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f82,plain,
    ( sK0 != sK3
    | spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_2
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f639,plain,
    ( spl4_36
    | ~ spl4_13
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f628,f593,f440,f636])).

fof(f440,plain,
    ( spl4_13
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f628,plain,
    ( k1_tarski(sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_13
    | ~ spl4_31 ),
    inference(forward_demodulation,[],[f442,f595])).

fof(f442,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f440])).

fof(f620,plain,
    ( spl4_31
    | spl4_34
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f613,f436,f618,f593])).

fof(f613,plain,
    ( ! [X2] :
        ( k1_tarski(X2) != k1_tarski(sK2)
        | sK0 = sK1 )
    | ~ spl4_12 ),
    inference(superposition,[],[f60,f438])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k5_enumset1(X1,X1,X1,X1,X1,X1,X2)
      | X1 = X2 ) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( X1 = X2
      | k2_tarski(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k1_tarski(X0)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f607,plain,
    ( spl4_33
    | spl4_2
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f600,f541,f80,f604])).

fof(f541,plain,
    ( spl4_24
  <=> r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f600,plain,
    ( sK0 = sK3
    | sK1 = sK3
    | ~ spl4_24 ),
    inference(resolution,[],[f543,f59])).

fof(f543,plain,
    ( r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f541])).

fof(f599,plain,
    ( spl4_31
    | spl4_32
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f583,f440,f597,f593])).

fof(f583,plain,
    ( ! [X2] :
        ( k1_tarski(X2) != k1_tarski(sK3)
        | sK0 = sK1 )
    | ~ spl4_13 ),
    inference(superposition,[],[f60,f442])).

fof(f544,plain,
    ( spl4_24
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f538,f386,f541])).

fof(f538,plain,
    ( r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_10 ),
    inference(superposition,[],[f70,f388])).

fof(f70,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(definition_unfolding,[],[f42,f57])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f461,plain,
    ( spl4_15
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f450,f432,f458])).

fof(f432,plain,
    ( spl4_11
  <=> k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f450,plain,
    ( r1_tarski(k1_tarski(sK0),k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f66,f434])).

fof(f434,plain,
    ( k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f432])).

fof(f443,plain,
    ( spl4_10
    | spl4_11
    | spl4_12
    | spl4_13
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f305,f91,f440,f436,f432,f386])).

fof(f91,plain,
    ( spl4_4
  <=> r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f305,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f65,f93])).

fof(f93,plain,
    ( r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f39,f57,f57])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f346,plain,
    ( ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f87,f331])).

fof(f331,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl4_8
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f332,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f264,f330,f327])).

fof(f264,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k1_xboole_0)
      | r1_tarski(k3_xboole_0(k1_xboole_0,X1),X2) ) ),
    inference(resolution,[],[f240,f141])).

fof(f141,plain,(
    ! [X8,X7,X9] :
      ( ~ r1_xboole_0(k3_xboole_0(X7,X8),X7)
      | r1_tarski(k3_xboole_0(X7,X8),X9) ) ),
    inference(resolution,[],[f137,f100])).

fof(f100,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X5,k3_xboole_0(X3,X4))
      | ~ r1_xboole_0(X5,X3) ) ),
    inference(superposition,[],[f55,f52])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f240,plain,(
    ! [X14,X12,X13] :
      ( r1_xboole_0(k3_xboole_0(X12,X13),k1_xboole_0)
      | ~ r1_xboole_0(X14,X12) ) ),
    inference(resolution,[],[f228,f100])).

fof(f228,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X7,X6)
      | r1_xboole_0(X6,k1_xboole_0) ) ),
    inference(resolution,[],[f222,f107])).

fof(f222,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f105,f67])).

fof(f105,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r1_tarski(k4_xboole_0(X2,X3),X4)
      | r1_xboole_0(X1,k1_xboole_0)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f102,f99])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X2,X0)
      | r1_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f99,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f58,f91])).

fof(f58,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f31,f57,f57])).

fof(f31,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f88,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f73,f85])).

fof(f73,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f80])).

fof(f33,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (8436)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (8423)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (8420)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (8425)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (8418)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (8425)Refutation not found, incomplete strategy% (8425)------------------------------
% 0.21/0.52  % (8425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8425)Memory used [KB]: 10618
% 0.21/0.52  % (8425)Time elapsed: 0.108 s
% 0.21/0.52  % (8425)------------------------------
% 0.21/0.52  % (8425)------------------------------
% 0.21/0.52  % (8414)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (8431)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (8417)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.52  % (8413)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.53  % (8439)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.25/0.53  % (8435)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.25/0.53  % (8441)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.25/0.53  % (8415)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.25/0.53  % (8427)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.25/0.53  % (8433)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.25/0.54  % (8437)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.25/0.54  % (8414)Refutation not found, incomplete strategy% (8414)------------------------------
% 1.25/0.54  % (8414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (8414)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (8414)Memory used [KB]: 1663
% 1.25/0.54  % (8414)Time elapsed: 0.136 s
% 1.25/0.54  % (8414)------------------------------
% 1.25/0.54  % (8414)------------------------------
% 1.25/0.54  % (8419)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.54  % (8438)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.41/0.54  % (8424)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.54  % (8429)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.54  % (8430)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.54  % (8421)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.41/0.54  % (8429)Refutation not found, incomplete strategy% (8429)------------------------------
% 1.41/0.54  % (8429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (8434)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.41/0.55  % (8428)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.41/0.55  % (8422)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.55  % (8442)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.55  % (8429)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (8429)Memory used [KB]: 10618
% 1.41/0.55  % (8429)Time elapsed: 0.139 s
% 1.41/0.55  % (8429)------------------------------
% 1.41/0.55  % (8429)------------------------------
% 1.41/0.56  % (8441)Refutation not found, incomplete strategy% (8441)------------------------------
% 1.41/0.56  % (8441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (8432)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.56  % (8426)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.56  % (8416)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.41/0.57  % (8436)Refutation found. Thanks to Tanya!
% 1.41/0.57  % SZS status Theorem for theBenchmark
% 1.41/0.57  % (8440)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.58  % (8441)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.58  
% 1.41/0.58  % (8441)Memory used [KB]: 11001
% 1.41/0.58  % (8441)Time elapsed: 0.154 s
% 1.41/0.58  % (8441)------------------------------
% 1.41/0.58  % (8441)------------------------------
% 1.41/0.58  % SZS output start Proof for theBenchmark
% 1.41/0.58  fof(f1004,plain,(
% 1.41/0.58    $false),
% 1.41/0.58    inference(avatar_sat_refutation,[],[f78,f83,f88,f94,f332,f346,f443,f461,f544,f599,f607,f620,f639,f651,f673,f756,f770,f792,f802,f874,f875,f953,f964,f972,f1003])).
% 1.41/0.58  fof(f1003,plain,(
% 1.41/0.58    spl4_31 | ~spl4_50 | ~spl4_52),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f999])).
% 1.41/0.58  fof(f999,plain,(
% 1.41/0.58    $false | (spl4_31 | ~spl4_50 | ~spl4_52)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f594,f66,f998])).
% 1.41/0.58  fof(f998,plain,(
% 1.41/0.58    ( ! [X1] : (~r1_tarski(k1_tarski(X1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X1) ) | (~spl4_50 | ~spl4_52)),
% 1.41/0.58    inference(duplicate_literal_removal,[],[f997])).
% 1.41/0.58  fof(f997,plain,(
% 1.41/0.58    ( ! [X1] : (sK1 = X1 | ~r1_tarski(k1_tarski(X1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X1) ) | (~spl4_50 | ~spl4_52)),
% 1.41/0.58    inference(forward_demodulation,[],[f956,f971])).
% 1.41/0.58  fof(f971,plain,(
% 1.41/0.58    sK1 = sK2 | ~spl4_52),
% 1.41/0.58    inference(avatar_component_clause,[],[f969])).
% 1.41/0.58  fof(f969,plain,(
% 1.41/0.58    spl4_52 <=> sK1 = sK2),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.41/0.58  fof(f956,plain,(
% 1.41/0.58    ( ! [X1] : (~r1_tarski(k1_tarski(X1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 = X1 | sK1 = X1) ) | ~spl4_50),
% 1.41/0.58    inference(superposition,[],[f59,f952])).
% 1.41/0.58  fof(f952,plain,(
% 1.41/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1) | ~spl4_50),
% 1.41/0.58    inference(avatar_component_clause,[],[f950])).
% 1.41/0.58  fof(f950,plain,(
% 1.41/0.58    spl4_50 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.41/0.58  fof(f59,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | X0 = X1 | X0 = X2) )),
% 1.41/0.58    inference(definition_unfolding,[],[f34,f57])).
% 1.41/0.58  fof(f57,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.41/0.58    inference(definition_unfolding,[],[f47,f53])).
% 1.41/0.58  fof(f53,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f8])).
% 1.41/0.58  fof(f8,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).
% 1.41/0.58  fof(f47,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f7])).
% 1.41/0.58  fof(f7,axiom,(
% 1.41/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.58  fof(f34,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.41/0.58    inference(cnf_transformation,[],[f17])).
% 1.41/0.58  fof(f17,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.41/0.58    inference(ennf_transformation,[],[f12])).
% 1.41/0.58  fof(f12,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.41/0.58  fof(f66,plain,(
% 1.41/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 1.41/0.58    inference(definition_unfolding,[],[f46,f57])).
% 1.41/0.58  fof(f46,plain,(
% 1.41/0.58    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.41/0.58    inference(cnf_transformation,[],[f10])).
% 1.41/0.58  fof(f10,axiom,(
% 1.41/0.58    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.41/0.58  fof(f594,plain,(
% 1.41/0.58    sK0 != sK1 | spl4_31),
% 1.41/0.58    inference(avatar_component_clause,[],[f593])).
% 1.41/0.58  fof(f593,plain,(
% 1.41/0.58    spl4_31 <=> sK0 = sK1),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.41/0.58  fof(f972,plain,(
% 1.41/0.58    spl4_52 | spl4_1 | ~spl4_51),
% 1.41/0.58    inference(avatar_split_clause,[],[f965,f961,f75,f969])).
% 1.41/0.58  fof(f75,plain,(
% 1.41/0.58    spl4_1 <=> sK0 = sK2),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.41/0.58  fof(f961,plain,(
% 1.41/0.58    spl4_51 <=> r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 1.41/0.58  fof(f965,plain,(
% 1.41/0.58    sK0 = sK2 | sK1 = sK2 | ~spl4_51),
% 1.41/0.58    inference(resolution,[],[f963,f59])).
% 1.41/0.58  fof(f963,plain,(
% 1.41/0.58    r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_51),
% 1.41/0.58    inference(avatar_component_clause,[],[f961])).
% 1.41/0.58  fof(f964,plain,(
% 1.41/0.58    spl4_51 | ~spl4_50),
% 1.41/0.58    inference(avatar_split_clause,[],[f959,f950,f961])).
% 1.41/0.58  fof(f959,plain,(
% 1.41/0.58    r1_tarski(k1_tarski(sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_50),
% 1.41/0.58    inference(superposition,[],[f66,f952])).
% 1.41/0.58  fof(f953,plain,(
% 1.41/0.58    spl4_50 | ~spl4_10 | ~spl4_33),
% 1.41/0.58    inference(avatar_split_clause,[],[f941,f604,f386,f950])).
% 1.41/0.58  fof(f386,plain,(
% 1.41/0.58    spl4_10 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.41/0.58  fof(f604,plain,(
% 1.41/0.58    spl4_33 <=> sK1 = sK3),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.41/0.58  fof(f941,plain,(
% 1.41/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1) | (~spl4_10 | ~spl4_33)),
% 1.41/0.58    inference(forward_demodulation,[],[f388,f606])).
% 1.41/0.58  fof(f606,plain,(
% 1.41/0.58    sK1 = sK3 | ~spl4_33),
% 1.41/0.58    inference(avatar_component_clause,[],[f604])).
% 1.41/0.58  fof(f388,plain,(
% 1.41/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) | ~spl4_10),
% 1.41/0.58    inference(avatar_component_clause,[],[f386])).
% 1.41/0.58  fof(f875,plain,(
% 1.41/0.58    sK0 != sK1 | sK1 != sK3 | sK0 = sK3),
% 1.41/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.41/0.58  fof(f874,plain,(
% 1.41/0.58    spl4_1 | ~spl4_3 | ~spl4_7 | ~spl4_39),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f869])).
% 1.41/0.58  fof(f869,plain,(
% 1.41/0.58    $false | (spl4_1 | ~spl4_3 | ~spl4_7 | ~spl4_39)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f77,f391,f825])).
% 1.41/0.58  fof(f825,plain,(
% 1.41/0.58    ( ! [X1] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X1)) | sK0 = X1) ) | ~spl4_39),
% 1.41/0.58    inference(superposition,[],[f48,f742])).
% 1.41/0.58  fof(f742,plain,(
% 1.41/0.58    k1_xboole_0 = k1_tarski(sK0) | ~spl4_39),
% 1.41/0.58    inference(avatar_component_clause,[],[f741])).
% 1.41/0.58  fof(f741,plain,(
% 1.41/0.58    spl4_39 <=> k1_xboole_0 = k1_tarski(sK0)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.41/0.58  fof(f48,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.41/0.58    inference(cnf_transformation,[],[f20])).
% 1.41/0.58  fof(f20,plain,(
% 1.41/0.58    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.41/0.58    inference(ennf_transformation,[],[f11])).
% 1.41/0.58  fof(f11,axiom,(
% 1.41/0.58    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 1.41/0.58  fof(f391,plain,(
% 1.41/0.58    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) ) | (~spl4_3 | ~spl4_7)),
% 1.41/0.58    inference(resolution,[],[f328,f152])).
% 1.41/0.58  fof(f152,plain,(
% 1.41/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_3),
% 1.41/0.58    inference(resolution,[],[f138,f38])).
% 1.41/0.58  fof(f38,plain,(
% 1.41/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f27])).
% 1.41/0.58  fof(f27,plain,(
% 1.41/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.58    inference(flattening,[],[f26])).
% 1.41/0.58  fof(f26,plain,(
% 1.41/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.58    inference(nnf_transformation,[],[f1])).
% 1.41/0.58  fof(f1,axiom,(
% 1.41/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.58  fof(f138,plain,(
% 1.41/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_3),
% 1.41/0.58    inference(resolution,[],[f137,f87])).
% 1.41/0.58  fof(f87,plain,(
% 1.41/0.58    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_3),
% 1.41/0.58    inference(avatar_component_clause,[],[f85])).
% 1.41/0.58  fof(f85,plain,(
% 1.41/0.58    spl4_3 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.41/0.58  fof(f137,plain,(
% 1.41/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(trivial_inequality_removal,[],[f130])).
% 1.41/0.58  fof(f130,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,X1) | ~r1_xboole_0(X0,X0)) )),
% 1.41/0.58    inference(superposition,[],[f44,f127])).
% 1.41/0.58  fof(f127,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X0)) )),
% 1.41/0.58    inference(resolution,[],[f111,f107])).
% 1.41/0.58  fof(f107,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X1,X0)) )),
% 1.41/0.58    inference(resolution,[],[f51,f99])).
% 1.41/0.58  fof(f99,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (r1_xboole_0(X2,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X2,X0)) )),
% 1.41/0.58    inference(superposition,[],[f56,f52])).
% 1.41/0.58  fof(f52,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.41/0.58    inference(cnf_transformation,[],[f3])).
% 1.41/0.58  fof(f3,axiom,(
% 1.41/0.58    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.41/0.58  fof(f56,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f23])).
% 1.41/0.58  fof(f23,plain,(
% 1.41/0.58    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.41/0.58    inference(ennf_transformation,[],[f5])).
% 1.41/0.58  fof(f5,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.41/0.58  fof(f51,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) )),
% 1.41/0.58    inference(cnf_transformation,[],[f22])).
% 1.41/0.58  fof(f22,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.41/0.58    inference(ennf_transformation,[],[f6])).
% 1.41/0.58  fof(f6,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.41/0.58  fof(f111,plain,(
% 1.41/0.58    ( ! [X4,X3] : (~r1_xboole_0(X3,k4_xboole_0(X3,X4)) | k1_xboole_0 = k4_xboole_0(X3,X4)) )),
% 1.41/0.58    inference(resolution,[],[f107,f50])).
% 1.41/0.58  fof(f50,plain,(
% 1.41/0.58    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.41/0.58    inference(cnf_transformation,[],[f21])).
% 1.41/0.58  fof(f21,plain,(
% 1.41/0.58    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.41/0.58    inference(ennf_transformation,[],[f4])).
% 1.41/0.58  fof(f4,axiom,(
% 1.41/0.58    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.41/0.58  fof(f44,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f30])).
% 1.41/0.58  fof(f30,plain,(
% 1.41/0.58    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.41/0.58    inference(nnf_transformation,[],[f2])).
% 1.41/0.58  fof(f2,axiom,(
% 1.41/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.41/0.58  fof(f328,plain,(
% 1.41/0.58    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(k1_xboole_0,X1),X2)) ) | ~spl4_7),
% 1.41/0.58    inference(avatar_component_clause,[],[f327])).
% 1.41/0.58  fof(f327,plain,(
% 1.41/0.58    spl4_7 <=> ! [X1,X2] : r1_tarski(k3_xboole_0(k1_xboole_0,X1),X2)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.41/0.58  fof(f77,plain,(
% 1.41/0.58    sK0 != sK2 | spl4_1),
% 1.41/0.58    inference(avatar_component_clause,[],[f75])).
% 1.41/0.58  fof(f802,plain,(
% 1.41/0.58    ~spl4_3 | ~spl4_15 | spl4_39),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f797])).
% 1.41/0.58  fof(f797,plain,(
% 1.41/0.58    $false | (~spl4_3 | ~spl4_15 | spl4_39)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f138,f743,f460,f38])).
% 1.41/0.58  fof(f460,plain,(
% 1.41/0.58    r1_tarski(k1_tarski(sK0),k1_xboole_0) | ~spl4_15),
% 1.41/0.58    inference(avatar_component_clause,[],[f458])).
% 1.41/0.58  fof(f458,plain,(
% 1.41/0.58    spl4_15 <=> r1_tarski(k1_tarski(sK0),k1_xboole_0)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.41/0.58  fof(f743,plain,(
% 1.41/0.58    k1_xboole_0 != k1_tarski(sK0) | spl4_39),
% 1.41/0.58    inference(avatar_component_clause,[],[f741])).
% 1.41/0.58  fof(f792,plain,(
% 1.41/0.58    ~spl4_34),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f780])).
% 1.41/0.58  fof(f780,plain,(
% 1.41/0.58    $false | ~spl4_34),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f67,f67,f619,f38])).
% 1.41/0.58  fof(f619,plain,(
% 1.41/0.58    ( ! [X2] : (k1_tarski(X2) != k1_tarski(sK2)) ) | ~spl4_34),
% 1.41/0.58    inference(avatar_component_clause,[],[f618])).
% 1.41/0.58  fof(f618,plain,(
% 1.41/0.58    spl4_34 <=> ! [X2] : k1_tarski(X2) != k1_tarski(sK2)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.41/0.58  fof(f67,plain,(
% 1.41/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.58    inference(equality_resolution,[],[f37])).
% 1.41/0.58  fof(f37,plain,(
% 1.41/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.41/0.58    inference(cnf_transformation,[],[f27])).
% 1.41/0.58  fof(f770,plain,(
% 1.41/0.58    spl4_1 | ~spl4_41),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f766])).
% 1.41/0.58  fof(f766,plain,(
% 1.41/0.58    $false | (spl4_1 | ~spl4_41)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f77,f67,f764])).
% 1.41/0.58  fof(f764,plain,(
% 1.41/0.58    ( ! [X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(sK2)) | sK0 = X1) ) | ~spl4_41),
% 1.41/0.58    inference(duplicate_literal_removal,[],[f760])).
% 1.41/0.58  fof(f760,plain,(
% 1.41/0.58    ( ! [X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(sK2)) | sK0 = X1 | sK0 = X1) ) | ~spl4_41),
% 1.41/0.58    inference(superposition,[],[f59,f755])).
% 1.41/0.58  fof(f755,plain,(
% 1.41/0.58    k1_tarski(sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_41),
% 1.41/0.58    inference(avatar_component_clause,[],[f753])).
% 1.41/0.58  fof(f753,plain,(
% 1.41/0.58    spl4_41 <=> k1_tarski(sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.41/0.58  fof(f756,plain,(
% 1.41/0.58    spl4_41 | ~spl4_12 | ~spl4_31),
% 1.41/0.58    inference(avatar_split_clause,[],[f739,f593,f436,f753])).
% 1.41/0.58  fof(f436,plain,(
% 1.41/0.58    spl4_12 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.41/0.58  fof(f739,plain,(
% 1.41/0.58    k1_tarski(sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl4_12 | ~spl4_31)),
% 1.41/0.58    inference(forward_demodulation,[],[f438,f595])).
% 1.41/0.58  fof(f595,plain,(
% 1.41/0.58    sK0 = sK1 | ~spl4_31),
% 1.41/0.58    inference(avatar_component_clause,[],[f593])).
% 1.41/0.58  fof(f438,plain,(
% 1.41/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2) | ~spl4_12),
% 1.41/0.58    inference(avatar_component_clause,[],[f436])).
% 1.41/0.58  fof(f673,plain,(
% 1.41/0.58    ~spl4_32),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f661])).
% 1.41/0.58  fof(f661,plain,(
% 1.41/0.58    $false | ~spl4_32),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f67,f67,f598,f38])).
% 1.41/0.58  fof(f598,plain,(
% 1.41/0.58    ( ! [X2] : (k1_tarski(X2) != k1_tarski(sK3)) ) | ~spl4_32),
% 1.41/0.58    inference(avatar_component_clause,[],[f597])).
% 1.41/0.58  fof(f597,plain,(
% 1.41/0.58    spl4_32 <=> ! [X2] : k1_tarski(X2) != k1_tarski(sK3)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.41/0.58  fof(f651,plain,(
% 1.41/0.58    spl4_2 | ~spl4_36),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f647])).
% 1.41/0.58  fof(f647,plain,(
% 1.41/0.58    $false | (spl4_2 | ~spl4_36)),
% 1.41/0.58    inference(unit_resulting_resolution,[],[f82,f67,f645])).
% 1.41/0.58  fof(f645,plain,(
% 1.41/0.58    ( ! [X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(sK3)) | sK0 = X1) ) | ~spl4_36),
% 1.41/0.58    inference(duplicate_literal_removal,[],[f641])).
% 1.41/0.58  fof(f641,plain,(
% 1.41/0.58    ( ! [X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(sK3)) | sK0 = X1 | sK0 = X1) ) | ~spl4_36),
% 1.41/0.58    inference(superposition,[],[f59,f638])).
% 1.41/0.58  fof(f638,plain,(
% 1.41/0.58    k1_tarski(sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl4_36),
% 1.41/0.58    inference(avatar_component_clause,[],[f636])).
% 1.41/0.58  fof(f636,plain,(
% 1.41/0.58    spl4_36 <=> k1_tarski(sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.41/0.58  fof(f82,plain,(
% 1.41/0.58    sK0 != sK3 | spl4_2),
% 1.41/0.58    inference(avatar_component_clause,[],[f80])).
% 1.41/0.58  fof(f80,plain,(
% 1.41/0.58    spl4_2 <=> sK0 = sK3),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.41/0.58  fof(f639,plain,(
% 1.41/0.58    spl4_36 | ~spl4_13 | ~spl4_31),
% 1.41/0.58    inference(avatar_split_clause,[],[f628,f593,f440,f636])).
% 1.41/0.58  fof(f440,plain,(
% 1.41/0.58    spl4_13 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.41/0.58  fof(f628,plain,(
% 1.41/0.58    k1_tarski(sK3) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl4_13 | ~spl4_31)),
% 1.41/0.58    inference(forward_demodulation,[],[f442,f595])).
% 1.41/0.58  fof(f442,plain,(
% 1.41/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3) | ~spl4_13),
% 1.41/0.58    inference(avatar_component_clause,[],[f440])).
% 1.41/0.58  fof(f620,plain,(
% 1.41/0.58    spl4_31 | spl4_34 | ~spl4_12),
% 1.41/0.58    inference(avatar_split_clause,[],[f613,f436,f618,f593])).
% 1.41/0.58  fof(f613,plain,(
% 1.41/0.58    ( ! [X2] : (k1_tarski(X2) != k1_tarski(sK2) | sK0 = sK1) ) | ~spl4_12),
% 1.41/0.58    inference(superposition,[],[f60,f438])).
% 1.41/0.58  fof(f60,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (k1_tarski(X0) != k5_enumset1(X1,X1,X1,X1,X1,X1,X2) | X1 = X2) )),
% 1.41/0.58    inference(definition_unfolding,[],[f35,f57])).
% 1.41/0.58  fof(f35,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (X1 = X2 | k2_tarski(X1,X2) != k1_tarski(X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f18])).
% 1.41/0.58  fof(f18,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (X1 = X2 | k2_tarski(X1,X2) != k1_tarski(X0))),
% 1.41/0.58    inference(ennf_transformation,[],[f13])).
% 1.41/0.58  fof(f13,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : (k2_tarski(X1,X2) = k1_tarski(X0) => X1 = X2)),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 1.41/0.58  fof(f607,plain,(
% 1.41/0.58    spl4_33 | spl4_2 | ~spl4_24),
% 1.41/0.58    inference(avatar_split_clause,[],[f600,f541,f80,f604])).
% 1.41/0.58  fof(f541,plain,(
% 1.41/0.58    spl4_24 <=> r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.41/0.58  fof(f600,plain,(
% 1.41/0.58    sK0 = sK3 | sK1 = sK3 | ~spl4_24),
% 1.41/0.58    inference(resolution,[],[f543,f59])).
% 1.41/0.58  fof(f543,plain,(
% 1.41/0.58    r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_24),
% 1.41/0.58    inference(avatar_component_clause,[],[f541])).
% 1.41/0.58  fof(f599,plain,(
% 1.41/0.58    spl4_31 | spl4_32 | ~spl4_13),
% 1.41/0.58    inference(avatar_split_clause,[],[f583,f440,f597,f593])).
% 1.41/0.58  fof(f583,plain,(
% 1.41/0.58    ( ! [X2] : (k1_tarski(X2) != k1_tarski(sK3) | sK0 = sK1) ) | ~spl4_13),
% 1.41/0.58    inference(superposition,[],[f60,f442])).
% 1.41/0.58  fof(f544,plain,(
% 1.41/0.58    spl4_24 | ~spl4_10),
% 1.41/0.58    inference(avatar_split_clause,[],[f538,f386,f541])).
% 1.41/0.58  fof(f538,plain,(
% 1.41/0.58    r1_tarski(k1_tarski(sK3),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_10),
% 1.41/0.58    inference(superposition,[],[f70,f388])).
% 1.41/0.58  fof(f70,plain,(
% 1.41/0.58    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) )),
% 1.41/0.58    inference(equality_resolution,[],[f62])).
% 1.41/0.58  fof(f62,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | k1_tarski(X2) != X0) )),
% 1.41/0.58    inference(definition_unfolding,[],[f42,f57])).
% 1.41/0.58  fof(f42,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.41/0.58    inference(cnf_transformation,[],[f29])).
% 1.41/0.58  fof(f29,plain,(
% 1.41/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.41/0.58    inference(flattening,[],[f28])).
% 1.41/0.58  fof(f28,plain,(
% 1.41/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.41/0.58    inference(nnf_transformation,[],[f19])).
% 1.41/0.58  fof(f19,plain,(
% 1.41/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.41/0.58    inference(ennf_transformation,[],[f9])).
% 1.41/0.58  fof(f9,axiom,(
% 1.41/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.41/0.58  fof(f461,plain,(
% 1.41/0.58    spl4_15 | ~spl4_11),
% 1.41/0.58    inference(avatar_split_clause,[],[f450,f432,f458])).
% 1.41/0.58  fof(f432,plain,(
% 1.41/0.58    spl4_11 <=> k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.41/0.58  fof(f450,plain,(
% 1.41/0.58    r1_tarski(k1_tarski(sK0),k1_xboole_0) | ~spl4_11),
% 1.41/0.58    inference(superposition,[],[f66,f434])).
% 1.41/0.58  fof(f434,plain,(
% 1.41/0.58    k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl4_11),
% 1.41/0.58    inference(avatar_component_clause,[],[f432])).
% 1.41/0.58  fof(f443,plain,(
% 1.41/0.58    spl4_10 | spl4_11 | spl4_12 | spl4_13 | ~spl4_4),
% 1.41/0.58    inference(avatar_split_clause,[],[f305,f91,f440,f436,f432,f386])).
% 1.41/0.58  fof(f91,plain,(
% 1.41/0.58    spl4_4 <=> r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.41/0.58  fof(f305,plain,(
% 1.41/0.58    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK3) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) | ~spl4_4),
% 1.41/0.58    inference(resolution,[],[f65,f93])).
% 1.41/0.58  fof(f93,plain,(
% 1.41/0.58    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl4_4),
% 1.41/0.58    inference(avatar_component_clause,[],[f91])).
% 1.41/0.58  fof(f65,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0) )),
% 1.41/0.58    inference(definition_unfolding,[],[f39,f57,f57])).
% 1.41/0.58  fof(f39,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.41/0.58    inference(cnf_transformation,[],[f29])).
% 1.41/0.58  fof(f346,plain,(
% 1.41/0.58    ~spl4_3 | ~spl4_8),
% 1.41/0.58    inference(avatar_contradiction_clause,[],[f342])).
% 1.41/0.58  fof(f342,plain,(
% 1.41/0.58    $false | (~spl4_3 | ~spl4_8)),
% 1.41/0.58    inference(subsumption_resolution,[],[f87,f331])).
% 1.41/0.58  fof(f331,plain,(
% 1.41/0.58    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_8),
% 1.41/0.58    inference(avatar_component_clause,[],[f330])).
% 1.41/0.58  fof(f330,plain,(
% 1.41/0.58    spl4_8 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 1.41/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.41/0.58  fof(f332,plain,(
% 1.41/0.58    spl4_7 | spl4_8),
% 1.41/0.58    inference(avatar_split_clause,[],[f264,f330,f327])).
% 1.41/0.58  fof(f264,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k1_xboole_0) | r1_tarski(k3_xboole_0(k1_xboole_0,X1),X2)) )),
% 1.41/0.58    inference(resolution,[],[f240,f141])).
% 1.41/0.58  fof(f141,plain,(
% 1.41/0.58    ( ! [X8,X7,X9] : (~r1_xboole_0(k3_xboole_0(X7,X8),X7) | r1_tarski(k3_xboole_0(X7,X8),X9)) )),
% 1.41/0.58    inference(resolution,[],[f137,f100])).
% 1.41/0.58  fof(f100,plain,(
% 1.41/0.58    ( ! [X4,X5,X3] : (r1_xboole_0(X5,k3_xboole_0(X3,X4)) | ~r1_xboole_0(X5,X3)) )),
% 1.41/0.58    inference(superposition,[],[f55,f52])).
% 1.41/0.58  fof(f55,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f23])).
% 1.41/0.58  fof(f240,plain,(
% 1.41/0.58    ( ! [X14,X12,X13] : (r1_xboole_0(k3_xboole_0(X12,X13),k1_xboole_0) | ~r1_xboole_0(X14,X12)) )),
% 1.41/0.58    inference(resolution,[],[f228,f100])).
% 1.41/0.58  fof(f228,plain,(
% 1.41/0.58    ( ! [X6,X7] : (~r1_xboole_0(X7,X6) | r1_xboole_0(X6,k1_xboole_0)) )),
% 1.41/0.58    inference(resolution,[],[f222,f107])).
% 1.41/0.58  fof(f222,plain,(
% 1.41/0.58    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X2,k1_xboole_0)) )),
% 1.41/0.58    inference(resolution,[],[f105,f67])).
% 1.41/0.58  fof(f105,plain,(
% 1.41/0.58    ( ! [X4,X2,X3,X1] : (~r1_tarski(k4_xboole_0(X2,X3),X4) | r1_xboole_0(X1,k1_xboole_0) | ~r1_xboole_0(X1,X2)) )),
% 1.41/0.58    inference(resolution,[],[f102,f99])).
% 1.41/0.58  fof(f102,plain,(
% 1.41/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,X0) | r1_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(superposition,[],[f99,f45])).
% 1.41/0.58  fof(f45,plain,(
% 1.41/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f30])).
% 1.41/0.58  fof(f94,plain,(
% 1.41/0.58    spl4_4),
% 1.41/0.58    inference(avatar_split_clause,[],[f58,f91])).
% 1.41/0.58  fof(f58,plain,(
% 1.41/0.58    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.41/0.58    inference(definition_unfolding,[],[f31,f57,f57])).
% 1.41/0.58  fof(f31,plain,(
% 1.41/0.58    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.41/0.58    inference(cnf_transformation,[],[f25])).
% 1.41/0.58  fof(f25,plain,(
% 1.41/0.58    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.41/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f24])).
% 1.41/0.58  fof(f24,plain,(
% 1.41/0.58    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.41/0.58    introduced(choice_axiom,[])).
% 1.41/0.58  fof(f16,plain,(
% 1.41/0.58    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.41/0.58    inference(ennf_transformation,[],[f15])).
% 1.41/0.58  fof(f15,negated_conjecture,(
% 1.41/0.58    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.41/0.58    inference(negated_conjecture,[],[f14])).
% 1.41/0.58  fof(f14,conjecture,(
% 1.41/0.58    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.41/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.41/0.58  fof(f88,plain,(
% 1.41/0.58    spl4_3),
% 1.41/0.58    inference(avatar_split_clause,[],[f73,f85])).
% 1.41/0.58  fof(f73,plain,(
% 1.41/0.58    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.41/0.58    inference(equality_resolution,[],[f49])).
% 1.41/0.58  fof(f49,plain,(
% 1.41/0.58    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.41/0.58    inference(cnf_transformation,[],[f21])).
% 1.41/0.58  fof(f83,plain,(
% 1.41/0.58    ~spl4_2),
% 1.41/0.58    inference(avatar_split_clause,[],[f33,f80])).
% 1.41/0.58  fof(f33,plain,(
% 1.41/0.58    sK0 != sK3),
% 1.41/0.58    inference(cnf_transformation,[],[f25])).
% 1.41/0.58  fof(f78,plain,(
% 1.41/0.58    ~spl4_1),
% 1.41/0.58    inference(avatar_split_clause,[],[f32,f75])).
% 1.41/0.58  fof(f32,plain,(
% 1.41/0.58    sK0 != sK2),
% 1.41/0.58    inference(cnf_transformation,[],[f25])).
% 1.41/0.58  % SZS output end Proof for theBenchmark
% 1.41/0.58  % (8436)------------------------------
% 1.41/0.58  % (8436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.58  % (8436)Termination reason: Refutation
% 1.41/0.58  
% 1.41/0.58  % (8436)Memory used [KB]: 11257
% 1.41/0.58  % (8436)Time elapsed: 0.167 s
% 1.41/0.58  % (8436)------------------------------
% 1.41/0.58  % (8436)------------------------------
% 1.41/0.59  % (8412)Success in time 0.225 s
%------------------------------------------------------------------------------
