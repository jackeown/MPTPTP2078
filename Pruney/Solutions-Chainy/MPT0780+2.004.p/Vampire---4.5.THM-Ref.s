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
% DateTime   : Thu Dec  3 12:55:56 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 197 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  262 ( 475 expanded)
%              Number of equality atoms :   43 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2025,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f95,f190,f225,f665,f674,f926,f956,f2023,f2024])).

fof(f2024,plain,
    ( ~ spl3_11
    | ~ spl3_74
    | spl3_10 ),
    inference(avatar_split_clause,[],[f1039,f179,f940,f183])).

fof(f183,plain,
    ( spl3_11
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f940,plain,
    ( spl3_74
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f179,plain,
    ( spl3_10
  <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1039,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_10 ),
    inference(resolution,[],[f229,f97])).

fof(f97,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(X1),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f59,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0))) ),
    inference(superposition,[],[f53,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f40,f40])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl3_10 ),
    inference(resolution,[],[f181,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f181,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f2023,plain,
    ( ~ spl3_1
    | ~ spl3_70
    | spl3_74 ),
    inference(avatar_split_clause,[],[f2016,f940,f923,f85])).

fof(f85,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f923,plain,
    ( spl3_70
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f2016,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | spl3_74 ),
    inference(resolution,[],[f959,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(f959,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl3_74 ),
    inference(resolution,[],[f942,f50])).

fof(f942,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_74 ),
    inference(avatar_component_clause,[],[f940])).

fof(f956,plain,(
    spl3_70 ),
    inference(avatar_contradiction_clause,[],[f954])).

fof(f954,plain,
    ( $false
    | spl3_70 ),
    inference(resolution,[],[f925,f34])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f925,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_70 ),
    inference(avatar_component_clause,[],[f923])).

fof(f926,plain,
    ( ~ spl3_1
    | ~ spl3_11
    | ~ spl3_70
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f913,f672,f923,f183,f85])).

fof(f672,plain,
    ( spl3_60
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v4_relat_1(k2_wellord1(sK2,sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f913,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_60 ),
    inference(resolution,[],[f673,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k2_wellord1(X0,X1),X1)
      | ~ v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f107,f44])).

fof(f107,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k3_relat_1(X3),X4)
      | v4_relat_1(X3,X4)
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k3_relat_1(X3),X4)
      | v4_relat_1(X3,X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f58,f98])).

fof(f98,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(X2),k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f53,f52])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(X0,X1)
      | v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f50,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f673,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(k2_wellord1(sK2,sK0),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f672])).

fof(f674,plain,
    ( ~ spl3_11
    | spl3_60
    | spl3_59 ),
    inference(avatar_split_clause,[],[f668,f662,f672,f183])).

fof(f662,plain,
    ( spl3_59
  <=> v4_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f668,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k2_wellord1(sK2,sK0))
        | ~ v4_relat_1(k2_wellord1(sK2,sK0),X0) )
    | spl3_59 ),
    inference(resolution,[],[f664,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f58,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f664,plain,
    ( ~ v4_relat_1(k2_wellord1(sK2,sK0),sK1)
    | spl3_59 ),
    inference(avatar_component_clause,[],[f662])).

fof(f665,plain,
    ( ~ spl3_11
    | ~ spl3_59
    | spl3_12 ),
    inference(avatar_split_clause,[],[f660,f187,f662,f183])).

fof(f187,plain,
    ( spl3_12
  <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f660,plain,
    ( ~ v4_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_12 ),
    inference(trivial_inequality_removal,[],[f659])).

fof(f659,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0)
    | ~ v4_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_12 ),
    inference(superposition,[],[f189,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f189,plain,
    ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f187])).

fof(f225,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f208,f33])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f208,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_11 ),
    inference(resolution,[],[f185,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f185,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f183])).

fof(f190,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | spl3_2 ),
    inference(avatar_split_clause,[],[f139,f89,f187,f183,f179])).

fof(f89,plain,
    ( spl3_2
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f139,plain,
    ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_2 ),
    inference(superposition,[],[f91,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f42,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(f91,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f95,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f87,f33])).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f93,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f80,f89,f85])).

fof(f80,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f35,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(f35,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:35:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.43  % (32533)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (32526)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (32523)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (32534)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (32537)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (32530)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (32529)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (32532)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (32527)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (32528)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (32539)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (32524)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (32540)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (32538)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (32525)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (32536)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.52  % (32535)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.31/0.52  % (32531)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.53/0.58  % (32527)Refutation found. Thanks to Tanya!
% 1.53/0.58  % SZS status Theorem for theBenchmark
% 1.53/0.58  % SZS output start Proof for theBenchmark
% 1.53/0.58  fof(f2025,plain,(
% 1.53/0.58    $false),
% 1.53/0.58    inference(avatar_sat_refutation,[],[f93,f95,f190,f225,f665,f674,f926,f956,f2023,f2024])).
% 1.53/0.58  fof(f2024,plain,(
% 1.53/0.58    ~spl3_11 | ~spl3_74 | spl3_10),
% 1.53/0.58    inference(avatar_split_clause,[],[f1039,f179,f940,f183])).
% 1.53/0.58  fof(f183,plain,(
% 1.53/0.58    spl3_11 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.53/0.58  fof(f940,plain,(
% 1.53/0.58    spl3_74 <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 1.53/0.58  fof(f179,plain,(
% 1.53/0.58    spl3_10 <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.53/0.58  fof(f1039,plain,(
% 1.53/0.58    ~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_10),
% 1.53/0.58    inference(resolution,[],[f229,f97])).
% 1.53/0.58  fof(f97,plain,(
% 1.53/0.58    ( ! [X1] : (r1_tarski(k2_relat_1(X1),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(superposition,[],[f59,f52])).
% 1.53/0.58  fof(f52,plain,(
% 1.53/0.58    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f36,f51])).
% 1.53/0.58  fof(f51,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f39,f40])).
% 1.53/0.58  fof(f40,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f4])).
% 1.53/0.58  fof(f4,axiom,(
% 1.53/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.58  fof(f39,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f5])).
% 1.53/0.58  fof(f5,axiom,(
% 1.53/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f18])).
% 1.53/0.58  fof(f18,plain,(
% 1.53/0.58    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f7])).
% 1.53/0.58  fof(f7,axiom,(
% 1.53/0.58    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.53/0.58  fof(f59,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X0)))) )),
% 1.53/0.58    inference(superposition,[],[f53,f54])).
% 1.53/0.58  fof(f54,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.53/0.58    inference(definition_unfolding,[],[f38,f40,f40])).
% 1.53/0.58  fof(f38,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f3])).
% 1.53/0.58  fof(f3,axiom,(
% 1.53/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.53/0.58  fof(f53,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 1.53/0.58    inference(definition_unfolding,[],[f37,f51])).
% 1.53/0.58  fof(f37,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f2])).
% 1.53/0.58  fof(f2,axiom,(
% 1.53/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.53/0.58  fof(f229,plain,(
% 1.53/0.58    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),X0) | ~r1_tarski(X0,sK1)) ) | spl3_10),
% 1.53/0.58    inference(resolution,[],[f181,f50])).
% 1.53/0.58  fof(f50,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f29])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.53/0.58    inference(flattening,[],[f28])).
% 1.53/0.58  fof(f28,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f1])).
% 1.53/0.58  fof(f1,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.53/0.58  fof(f181,plain,(
% 1.53/0.58    ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_10),
% 1.53/0.58    inference(avatar_component_clause,[],[f179])).
% 1.53/0.58  fof(f2023,plain,(
% 1.53/0.58    ~spl3_1 | ~spl3_70 | spl3_74),
% 1.53/0.58    inference(avatar_split_clause,[],[f2016,f940,f923,f85])).
% 1.53/0.58  fof(f85,plain,(
% 1.53/0.58    spl3_1 <=> v1_relat_1(sK2)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.53/0.58  fof(f923,plain,(
% 1.53/0.58    spl3_70 <=> r1_tarski(sK0,sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 1.53/0.58  fof(f2016,plain,(
% 1.53/0.58    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK2) | spl3_74),
% 1.53/0.58    inference(resolution,[],[f959,f44])).
% 1.53/0.58  fof(f44,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f21])).
% 1.53/0.58  fof(f21,plain,(
% 1.53/0.58    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f12])).
% 1.53/0.58  fof(f12,axiom,(
% 1.53/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).
% 1.53/0.58  fof(f959,plain,(
% 1.53/0.58    ( ! [X0] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),X0) | ~r1_tarski(X0,sK1)) ) | spl3_74),
% 1.53/0.58    inference(resolution,[],[f942,f50])).
% 1.53/0.58  fof(f942,plain,(
% 1.53/0.58    ~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_74),
% 1.53/0.58    inference(avatar_component_clause,[],[f940])).
% 1.53/0.58  fof(f956,plain,(
% 1.53/0.58    spl3_70),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f954])).
% 1.53/0.58  fof(f954,plain,(
% 1.53/0.58    $false | spl3_70),
% 1.53/0.58    inference(resolution,[],[f925,f34])).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    r1_tarski(sK0,sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f31,plain,(
% 1.53/0.58    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30])).
% 1.53/0.58  fof(f30,plain,(
% 1.53/0.58    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f17,plain,(
% 1.53/0.58    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.53/0.58    inference(flattening,[],[f16])).
% 1.53/0.58  fof(f16,plain,(
% 1.53/0.58    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.53/0.58    inference(ennf_transformation,[],[f15])).
% 1.53/0.58  fof(f15,negated_conjecture,(
% 1.53/0.58    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.53/0.58    inference(negated_conjecture,[],[f14])).
% 1.53/0.58  fof(f14,conjecture,(
% 1.53/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 1.53/0.58  fof(f925,plain,(
% 1.53/0.58    ~r1_tarski(sK0,sK1) | spl3_70),
% 1.53/0.58    inference(avatar_component_clause,[],[f923])).
% 1.53/0.58  fof(f926,plain,(
% 1.53/0.58    ~spl3_1 | ~spl3_11 | ~spl3_70 | ~spl3_60),
% 1.53/0.58    inference(avatar_split_clause,[],[f913,f672,f923,f183,f85])).
% 1.53/0.58  fof(f672,plain,(
% 1.53/0.58    spl3_60 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~v4_relat_1(k2_wellord1(sK2,sK0),X0))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.53/0.58  fof(f913,plain,(
% 1.53/0.58    ~r1_tarski(sK0,sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl3_60),
% 1.53/0.58    inference(resolution,[],[f673,f109])).
% 1.53/0.58  fof(f109,plain,(
% 1.53/0.58    ( ! [X0,X1] : (v4_relat_1(k2_wellord1(X0,X1),X1) | ~v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(resolution,[],[f107,f44])).
% 1.53/0.58  fof(f107,plain,(
% 1.53/0.58    ( ! [X4,X3] : (~r1_tarski(k3_relat_1(X3),X4) | v4_relat_1(X3,X4) | ~v1_relat_1(X3)) )),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f103])).
% 1.53/0.58  fof(f103,plain,(
% 1.53/0.58    ( ! [X4,X3] : (~r1_tarski(k3_relat_1(X3),X4) | v4_relat_1(X3,X4) | ~v1_relat_1(X3) | ~v1_relat_1(X3)) )),
% 1.53/0.58    inference(resolution,[],[f58,f98])).
% 1.53/0.58  fof(f98,plain,(
% 1.53/0.58    ( ! [X2] : (r1_tarski(k1_relat_1(X2),k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.53/0.58    inference(superposition,[],[f53,f52])).
% 1.53/0.58  fof(f58,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(X0,X1) | v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 1.53/0.58    inference(resolution,[],[f50,f47])).
% 1.53/0.58  fof(f47,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f32])).
% 1.53/0.58  fof(f32,plain,(
% 1.53/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(nnf_transformation,[],[f24])).
% 1.53/0.58  fof(f24,plain,(
% 1.53/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f6])).
% 1.53/0.58  fof(f6,axiom,(
% 1.53/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.53/0.58  fof(f673,plain,(
% 1.53/0.58    ( ! [X0] : (~v4_relat_1(k2_wellord1(sK2,sK0),X0) | ~r1_tarski(X0,sK1)) ) | ~spl3_60),
% 1.53/0.58    inference(avatar_component_clause,[],[f672])).
% 1.53/0.58  fof(f674,plain,(
% 1.53/0.58    ~spl3_11 | spl3_60 | spl3_59),
% 1.53/0.58    inference(avatar_split_clause,[],[f668,f662,f672,f183])).
% 1.53/0.58  fof(f662,plain,(
% 1.53/0.58    spl3_59 <=> v4_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 1.53/0.58  fof(f668,plain,(
% 1.53/0.58    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~v4_relat_1(k2_wellord1(sK2,sK0),X0)) ) | spl3_59),
% 1.53/0.58    inference(resolution,[],[f664,f108])).
% 1.53/0.58  fof(f108,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v4_relat_1(X2,X0)) )),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f102])).
% 1.53/0.58  fof(f102,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | v4_relat_1(X2,X1) | ~v1_relat_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 1.53/0.58    inference(resolution,[],[f58,f46])).
% 1.53/0.58  fof(f46,plain,(
% 1.53/0.58    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f32])).
% 1.53/0.58  fof(f664,plain,(
% 1.53/0.58    ~v4_relat_1(k2_wellord1(sK2,sK0),sK1) | spl3_59),
% 1.53/0.58    inference(avatar_component_clause,[],[f662])).
% 1.53/0.58  fof(f665,plain,(
% 1.53/0.58    ~spl3_11 | ~spl3_59 | spl3_12),
% 1.53/0.58    inference(avatar_split_clause,[],[f660,f187,f662,f183])).
% 1.53/0.58  fof(f187,plain,(
% 1.53/0.58    spl3_12 <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.53/0.58  fof(f660,plain,(
% 1.53/0.58    ~v4_relat_1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_12),
% 1.53/0.58    inference(trivial_inequality_removal,[],[f659])).
% 1.53/0.58  fof(f659,plain,(
% 1.53/0.58    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) | ~v4_relat_1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_12),
% 1.53/0.58    inference(superposition,[],[f189,f48])).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f26])).
% 1.53/0.58  fof(f26,plain,(
% 1.53/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(flattening,[],[f25])).
% 1.53/0.58  fof(f25,plain,(
% 1.53/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.53/0.58    inference(ennf_transformation,[],[f9])).
% 1.53/0.58  fof(f9,axiom,(
% 1.53/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.53/0.58  fof(f189,plain,(
% 1.53/0.58    k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) | spl3_12),
% 1.53/0.58    inference(avatar_component_clause,[],[f187])).
% 1.53/0.58  fof(f225,plain,(
% 1.53/0.58    spl3_11),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f224])).
% 1.53/0.58  fof(f224,plain,(
% 1.53/0.58    $false | spl3_11),
% 1.53/0.58    inference(resolution,[],[f208,f33])).
% 1.53/0.58  fof(f33,plain,(
% 1.53/0.58    v1_relat_1(sK2)),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  fof(f208,plain,(
% 1.53/0.58    ~v1_relat_1(sK2) | spl3_11),
% 1.53/0.58    inference(resolution,[],[f185,f41])).
% 1.53/0.58  fof(f41,plain,(
% 1.53/0.58    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f19])).
% 1.53/0.58  fof(f19,plain,(
% 1.53/0.58    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f10])).
% 1.53/0.58  fof(f10,axiom,(
% 1.53/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.53/0.58  fof(f185,plain,(
% 1.53/0.58    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_11),
% 1.53/0.58    inference(avatar_component_clause,[],[f183])).
% 1.53/0.58  fof(f190,plain,(
% 1.53/0.58    ~spl3_10 | ~spl3_11 | ~spl3_12 | spl3_2),
% 1.53/0.58    inference(avatar_split_clause,[],[f139,f89,f187,f183,f179])).
% 1.53/0.58  fof(f89,plain,(
% 1.53/0.58    spl3_2 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.53/0.58  fof(f139,plain,(
% 1.53/0.58    k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_2),
% 1.53/0.58    inference(superposition,[],[f91,f69])).
% 1.53/0.58  fof(f69,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0)) )),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f68])).
% 1.53/0.58  fof(f68,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(superposition,[],[f42,f45])).
% 1.53/0.58  fof(f45,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f23])).
% 1.53/0.58  fof(f23,plain,(
% 1.53/0.58    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(flattening,[],[f22])).
% 1.53/0.58  fof(f22,plain,(
% 1.53/0.58    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f8])).
% 1.53/0.58  fof(f8,axiom,(
% 1.53/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.53/0.58  fof(f42,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f20])).
% 1.53/0.58  fof(f20,plain,(
% 1.53/0.58    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f11])).
% 1.53/0.58  fof(f11,axiom,(
% 1.53/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).
% 1.53/0.58  fof(f91,plain,(
% 1.53/0.58    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | spl3_2),
% 1.53/0.58    inference(avatar_component_clause,[],[f89])).
% 1.53/0.58  fof(f95,plain,(
% 1.53/0.58    spl3_1),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f94])).
% 1.53/0.58  fof(f94,plain,(
% 1.53/0.58    $false | spl3_1),
% 1.53/0.58    inference(resolution,[],[f87,f33])).
% 1.53/0.58  fof(f87,plain,(
% 1.53/0.58    ~v1_relat_1(sK2) | spl3_1),
% 1.53/0.58    inference(avatar_component_clause,[],[f85])).
% 1.53/0.58  fof(f93,plain,(
% 1.53/0.58    ~spl3_1 | ~spl3_2),
% 1.53/0.58    inference(avatar_split_clause,[],[f80,f89,f85])).
% 1.53/0.58  fof(f80,plain,(
% 1.53/0.58    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 1.53/0.58    inference(superposition,[],[f35,f49])).
% 1.53/0.58  fof(f49,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f27])).
% 1.53/0.58  fof(f27,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 1.53/0.58    inference(ennf_transformation,[],[f13])).
% 1.53/0.58  fof(f13,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 1.53/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).
% 1.53/0.58  fof(f35,plain,(
% 1.53/0.58    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.53/0.58    inference(cnf_transformation,[],[f31])).
% 1.53/0.58  % SZS output end Proof for theBenchmark
% 1.53/0.58  % (32527)------------------------------
% 1.53/0.58  % (32527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (32527)Termination reason: Refutation
% 1.53/0.58  
% 1.53/0.58  % (32527)Memory used [KB]: 7291
% 1.53/0.58  % (32527)Time elapsed: 0.160 s
% 1.53/0.58  % (32527)------------------------------
% 1.53/0.58  % (32527)------------------------------
% 1.53/0.58  % (32522)Success in time 0.222 s
%------------------------------------------------------------------------------
