%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 189 expanded)
%              Number of leaves         :   24 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  267 ( 457 expanded)
%              Number of equality atoms :   43 (  91 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f92,f190,f239,f450,f685,f694,f1034,f1053,f1476])).

fof(f1476,plain,
    ( ~ spl3_1
    | ~ spl3_85
    | spl3_28 ),
    inference(avatar_split_clause,[],[f1471,f447,f1031,f82])).

fof(f82,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1031,plain,
    ( spl3_85
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f447,plain,
    ( spl3_28
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1471,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK2)
    | spl3_28 ),
    inference(resolution,[],[f462,f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

fof(f462,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl3_28 ),
    inference(resolution,[],[f449,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f449,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f447])).

fof(f1053,plain,(
    spl3_85 ),
    inference(avatar_contradiction_clause,[],[f1051])).

fof(f1051,plain,
    ( $false
    | spl3_85 ),
    inference(resolution,[],[f1033,f35])).

fof(f35,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31])).

fof(f31,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f1033,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_85 ),
    inference(avatar_component_clause,[],[f1031])).

fof(f1034,plain,
    ( ~ spl3_1
    | ~ spl3_11
    | ~ spl3_85
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f1024,f692,f1031,f183,f82])).

fof(f183,plain,
    ( spl3_11
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f692,plain,
    ( spl3_62
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v4_relat_1(k2_wellord1(sK2,sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f1024,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_62 ),
    inference(resolution,[],[f693,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k2_wellord1(X0,X1),X1)
      | ~ v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f96,f44])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_relat_1(X0),X1)
      | ~ v1_relat_1(X0)
      | v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f94,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f94,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_relat_1(X2),X3)
      | ~ r1_tarski(k3_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f55,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f693,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(k2_wellord1(sK2,sK0),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f692])).

fof(f694,plain,
    ( ~ spl3_11
    | spl3_62
    | spl3_61 ),
    inference(avatar_split_clause,[],[f688,f682,f692,f183])).

fof(f682,plain,
    ( spl3_61
  <=> v4_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f688,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k2_wellord1(sK2,sK0))
        | ~ v4_relat_1(k2_wellord1(sK2,sK0),X0) )
    | spl3_61 ),
    inference(resolution,[],[f684,f103])).

fof(f103,plain,(
    ! [X4,X5,X3] :
      ( v4_relat_1(X5,X4)
      | ~ r1_tarski(X3,X4)
      | ~ v1_relat_1(X5)
      | ~ v4_relat_1(X5,X3) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | v4_relat_1(X5,X4)
      | ~ v1_relat_1(X5)
      | ~ v4_relat_1(X5,X3)
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f58,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(X0,X1)
      | v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f51,f47])).

fof(f684,plain,
    ( ~ v4_relat_1(k2_wellord1(sK2,sK0),sK1)
    | spl3_61 ),
    inference(avatar_component_clause,[],[f682])).

fof(f685,plain,
    ( ~ spl3_11
    | ~ spl3_61
    | spl3_12 ),
    inference(avatar_split_clause,[],[f680,f187,f682,f183])).

fof(f187,plain,
    ( spl3_12
  <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f680,plain,
    ( ~ v4_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_12 ),
    inference(trivial_inequality_removal,[],[f679])).

fof(f679,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f189,plain,
    ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f187])).

fof(f450,plain,
    ( ~ spl3_11
    | ~ spl3_28
    | spl3_10 ),
    inference(avatar_split_clause,[],[f442,f179,f447,f183])).

fof(f179,plain,
    ( spl3_10
  <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f442,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_10 ),
    inference(resolution,[],[f181,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X1)
      | ~ r1_tarski(k3_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f60,f53])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k1_enumset1(X1,X1,X0)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f38,f40,f40])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f181,plain,
    ( ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f179])).

fof(f239,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f221,f34])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f221,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f185,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f183])).

fof(f190,plain,
    ( ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | spl3_2 ),
    inference(avatar_split_clause,[],[f138,f86,f187,f183,f179])).

fof(f86,plain,
    ( spl3_2
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f138,plain,
    ( k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | ~ r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | spl3_2 ),
    inference(superposition,[],[f88,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

fof(f88,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f92,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f84,f34])).

fof(f84,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f90,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f77,f86,f82])).

fof(f77,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f36,f49])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f36,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:22:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (1861)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  % (1864)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (1863)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (1874)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (1866)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (1870)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (1871)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (1872)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (1862)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (1869)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (1865)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (1858)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (1868)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (1876)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (1867)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (1875)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (1873)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (1860)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.52  % (1863)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1477,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f90,f92,f190,f239,f450,f685,f694,f1034,f1053,f1476])).
% 0.21/0.52  fof(f1476,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_85 | spl3_28),
% 0.21/0.52    inference(avatar_split_clause,[],[f1471,f447,f1031,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl3_1 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f1031,plain,(
% 0.21/0.52    spl3_85 <=> r1_tarski(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 0.21/0.52  fof(f447,plain,(
% 0.21/0.52    spl3_28 <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.52  fof(f1471,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK2) | spl3_28),
% 0.21/0.52    inference(resolution,[],[f462,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).
% 0.21/0.52  fof(f462,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),X0) | ~r1_tarski(X0,sK1)) ) | spl3_28),
% 0.21/0.52    inference(resolution,[],[f449,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.52  fof(f449,plain,(
% 0.21/0.52    ~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f447])).
% 0.21/0.52  fof(f1053,plain,(
% 0.21/0.52    spl3_85),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1051])).
% 0.21/0.52  fof(f1051,plain,(
% 0.21/0.52    $false | spl3_85),
% 0.21/0.52    inference(resolution,[],[f1033,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    r1_tarski(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f14])).
% 0.21/0.52  fof(f14,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).
% 0.21/0.52  fof(f1033,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK1) | spl3_85),
% 0.21/0.52    inference(avatar_component_clause,[],[f1031])).
% 0.21/0.52  fof(f1034,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_11 | ~spl3_85 | ~spl3_62),
% 0.21/0.52    inference(avatar_split_clause,[],[f1024,f692,f1031,f183,f82])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl3_11 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f692,plain,(
% 0.21/0.52    spl3_62 <=> ! [X0] : (~r1_tarski(X0,sK1) | ~v4_relat_1(k2_wellord1(sK2,sK0),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.52  fof(f1024,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl3_62),
% 0.21/0.52    inference(resolution,[],[f693,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v4_relat_1(k2_wellord1(X0,X1),X1) | ~v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f96,f44])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k3_relat_1(X0),X1) | ~v1_relat_1(X0) | v4_relat_1(X0,X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k3_relat_1(X0),X1) | ~v1_relat_1(X0) | v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f94,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X2,X3] : (r1_tarski(k1_relat_1(X2),X3) | ~r1_tarski(k3_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(superposition,[],[f55,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f37,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f39,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f50,f52])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.52  fof(f693,plain,(
% 0.21/0.52    ( ! [X0] : (~v4_relat_1(k2_wellord1(sK2,sK0),X0) | ~r1_tarski(X0,sK1)) ) | ~spl3_62),
% 0.21/0.52    inference(avatar_component_clause,[],[f692])).
% 0.21/0.52  fof(f694,plain,(
% 0.21/0.52    ~spl3_11 | spl3_62 | spl3_61),
% 0.21/0.52    inference(avatar_split_clause,[],[f688,f682,f692,f183])).
% 0.21/0.52  fof(f682,plain,(
% 0.21/0.52    spl3_61 <=> v4_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.21/0.52  fof(f688,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~v4_relat_1(k2_wellord1(sK2,sK0),X0)) ) | spl3_61),
% 0.21/0.52    inference(resolution,[],[f684,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (v4_relat_1(X5,X4) | ~r1_tarski(X3,X4) | ~v1_relat_1(X5) | ~v4_relat_1(X5,X3)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | v4_relat_1(X5,X4) | ~v1_relat_1(X5) | ~v4_relat_1(X5,X3) | ~v1_relat_1(X5)) )),
% 0.21/0.52    inference(resolution,[],[f58,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(X0,X1) | v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(resolution,[],[f51,f47])).
% 0.21/0.52  fof(f684,plain,(
% 0.21/0.52    ~v4_relat_1(k2_wellord1(sK2,sK0),sK1) | spl3_61),
% 0.21/0.52    inference(avatar_component_clause,[],[f682])).
% 0.21/0.52  fof(f685,plain,(
% 0.21/0.52    ~spl3_11 | ~spl3_61 | spl3_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f680,f187,f682,f183])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    spl3_12 <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f680,plain,(
% 0.21/0.52    ~v4_relat_1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_12),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f679])).
% 0.21/0.52  fof(f679,plain,(
% 0.21/0.52    k2_wellord1(sK2,sK0) != k2_wellord1(sK2,sK0) | ~v4_relat_1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_12),
% 0.21/0.52    inference(superposition,[],[f189,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) | spl3_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f187])).
% 0.21/0.52  fof(f450,plain,(
% 0.21/0.52    ~spl3_11 | ~spl3_28 | spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f442,f179,f447,f183])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    spl3_10 <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f442,plain,(
% 0.21/0.52    ~r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_10),
% 0.21/0.52    inference(resolution,[],[f181,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),X1) | ~r1_tarski(k3_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(superposition,[],[f60,f53])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k1_enumset1(X1,X1,X0)),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.52    inference(superposition,[],[f55,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f38,f40,f40])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f179])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    spl3_11),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    $false | spl3_11),
% 0.21/0.52    inference(resolution,[],[f221,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | spl3_11),
% 0.21/0.52    inference(resolution,[],[f185,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f183])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    ~spl3_10 | ~spl3_11 | ~spl3_12 | spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f138,f86,f187,f183,f179])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl3_2 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(k2_wellord1(sK2,sK0)) | ~r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | spl3_2),
% 0.21/0.52    inference(superposition,[],[f88,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(superposition,[],[f42,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f91])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    $false | spl3_1),
% 0.21/0.52    inference(resolution,[],[f84,f34])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f77,f86,f82])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | ~v1_relat_1(sK2)),
% 0.21/0.52    inference(superposition,[],[f36,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (1863)------------------------------
% 0.21/0.52  % (1863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1863)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (1863)Memory used [KB]: 7036
% 0.21/0.52  % (1863)Time elapsed: 0.101 s
% 0.21/0.52  % (1863)------------------------------
% 0.21/0.52  % (1863)------------------------------
% 0.21/0.52  % (1855)Success in time 0.161 s
%------------------------------------------------------------------------------
