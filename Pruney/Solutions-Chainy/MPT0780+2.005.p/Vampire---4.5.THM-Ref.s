%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:57 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 205 expanded)
%              Number of leaves         :   27 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :  243 ( 415 expanded)
%              Number of equality atoms :   51 ( 102 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1278,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f219,f380,f621,f650,f676,f683,f710,f1276,f1277])).

fof(f1277,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1276,plain,
    ( spl4_75
    | ~ spl4_3
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f1271,f643,f69,f1273])).

fof(f1273,plain,
    ( spl4_75
  <=> k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f69,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f643,plain,
    ( spl4_41
  <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f1271,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl4_3
    | ~ spl4_41 ),
    inference(superposition,[],[f84,f645])).

fof(f645,plain,
    ( k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f643])).

fof(f84,plain,
    ( ! [X2,X1] : k2_wellord1(k2_wellord1(sK2,X1),X2) = k7_relat_1(k8_relat_1(X2,k2_wellord1(sK2,X1)),X2)
    | ~ spl4_3 ),
    inference(resolution,[],[f41,f73])).

fof(f73,plain,
    ( ! [X0] : v1_relat_1(k2_wellord1(sK2,X0))
    | ~ spl4_3 ),
    inference(resolution,[],[f40,f71])).

fof(f71,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(f710,plain,
    ( spl4_48
    | ~ spl4_42
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f702,f673,f647,f707])).

fof(f707,plain,
    ( spl4_48
  <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f647,plain,
    ( spl4_42
  <=> v1_relat_1(k2_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f673,plain,
    ( spl4_45
  <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f702,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)
    | ~ spl4_45 ),
    inference(resolution,[],[f675,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f675,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f673])).

fof(f683,plain,
    ( ~ spl4_3
    | spl4_42 ),
    inference(avatar_contradiction_clause,[],[f682])).

fof(f682,plain,
    ( $false
    | ~ spl4_3
    | spl4_42 ),
    inference(resolution,[],[f649,f73])).

fof(f649,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f647])).

fof(f676,plain,
    ( spl4_45
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f660,f377,f69,f673])).

fof(f377,plain,
    ( spl4_24
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f660,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f473,f379])).

fof(f379,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f377])).

fof(f473,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,X4)),X5)
        | r1_tarski(k1_relat_1(k2_wellord1(sK2,X4)),X5) )
    | ~ spl4_3 ),
    inference(superposition,[],[f57,f177])).

fof(f177,plain,
    ( ! [X0] : k3_relat_1(k2_wellord1(sK2,X0)) = k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k2_relat_1(k2_wellord1(sK2,X0))))
    | ~ spl4_3 ),
    inference(resolution,[],[f55,f73])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f36,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f650,plain,
    ( spl4_41
    | ~ spl4_42
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f638,f618,f647,f643])).

fof(f618,plain,
    ( spl4_38
  <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f638,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,sK0))
    | k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))
    | ~ spl4_38 ),
    inference(resolution,[],[f620,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f620,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f618])).

fof(f621,plain,
    ( spl4_38
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f605,f377,f69,f618])).

fof(f605,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f470,f379])).

fof(f470,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1)
        | r1_tarski(k2_relat_1(k2_wellord1(sK2,X0)),X1) )
    | ~ spl4_3 ),
    inference(superposition,[],[f147,f177])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X0)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f37,f53,f53])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f380,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f357,f69,f64,f377])).

fof(f64,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f357,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f320,f66])).

fof(f66,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f320,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X2)),X3) )
    | ~ spl4_3 ),
    inference(resolution,[],[f318,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f318,plain,
    ( ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,
    ( ! [X0] :
        ( r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f265,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f265,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(k3_relat_1(k2_wellord1(sK2,X0)),X1),X0)
        | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f117,f71])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(k3_relat_1(k2_wellord1(X0,X1)),X2),X1)
      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2) ) ),
    inference(resolution,[],[f50,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(f219,plain,
    ( ~ spl4_14
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f211,f69,f59,f215])).

fof(f215,plain,
    ( spl4_14
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f59,plain,
    ( spl4_1
  <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f211,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(superposition,[],[f61,f166])).

fof(f166,plain,
    ( ! [X0,X1] : k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f48,f71])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

fof(f61,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f72,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

fof(f67,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:03:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (23630)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (23648)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (23652)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (23643)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (23628)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (23640)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (23638)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (23653)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (23633)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (23650)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (23652)Refutation not found, incomplete strategy% (23652)------------------------------
% 0.22/0.53  % (23652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23652)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23652)Memory used [KB]: 10746
% 0.22/0.53  % (23652)Time elapsed: 0.113 s
% 0.22/0.53  % (23652)------------------------------
% 0.22/0.53  % (23652)------------------------------
% 0.22/0.53  % (23661)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (23637)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (23645)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (23632)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (23627)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (23639)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (23657)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (23647)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (23654)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (23647)Refutation not found, incomplete strategy% (23647)------------------------------
% 0.22/0.55  % (23647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23647)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23647)Memory used [KB]: 10618
% 0.22/0.55  % (23647)Time elapsed: 0.130 s
% 0.22/0.55  % (23647)------------------------------
% 0.22/0.55  % (23647)------------------------------
% 0.22/0.55  % (23658)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (23634)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (23655)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (23641)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.55  % (23646)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.55  % (23649)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.56  % (23659)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.56  % (23635)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.46/0.56  % (23651)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.56  % (23644)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.56  % (23642)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.59/0.61  % (23646)Refutation found. Thanks to Tanya!
% 1.59/0.61  % SZS status Theorem for theBenchmark
% 1.59/0.61  % SZS output start Proof for theBenchmark
% 1.59/0.61  fof(f1278,plain,(
% 1.59/0.61    $false),
% 1.59/0.61    inference(avatar_sat_refutation,[],[f62,f67,f72,f219,f380,f621,f650,f676,f683,f710,f1276,f1277])).
% 1.59/0.61  fof(f1277,plain,(
% 1.59/0.61    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) | k2_wellord1(sK2,sK0) != k7_relat_1(k2_wellord1(sK2,sK0),sK1) | k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 1.59/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.59/0.61  fof(f1276,plain,(
% 1.59/0.61    spl4_75 | ~spl4_3 | ~spl4_41),
% 1.59/0.61    inference(avatar_split_clause,[],[f1271,f643,f69,f1273])).
% 1.59/0.61  fof(f1273,plain,(
% 1.59/0.61    spl4_75 <=> k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 1.59/0.61  fof(f69,plain,(
% 1.59/0.61    spl4_3 <=> v1_relat_1(sK2)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.59/0.61  fof(f643,plain,(
% 1.59/0.61    spl4_41 <=> k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.59/0.61  fof(f1271,plain,(
% 1.59/0.61    k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | (~spl4_3 | ~spl4_41)),
% 1.59/0.61    inference(superposition,[],[f84,f645])).
% 1.59/0.61  fof(f645,plain,(
% 1.59/0.61    k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~spl4_41),
% 1.59/0.61    inference(avatar_component_clause,[],[f643])).
% 1.59/0.61  fof(f84,plain,(
% 1.59/0.61    ( ! [X2,X1] : (k2_wellord1(k2_wellord1(sK2,X1),X2) = k7_relat_1(k8_relat_1(X2,k2_wellord1(sK2,X1)),X2)) ) | ~spl4_3),
% 1.59/0.61    inference(resolution,[],[f41,f73])).
% 1.59/0.61  fof(f73,plain,(
% 1.59/0.61    ( ! [X0] : (v1_relat_1(k2_wellord1(sK2,X0))) ) | ~spl4_3),
% 1.59/0.61    inference(resolution,[],[f40,f71])).
% 1.59/0.61  fof(f71,plain,(
% 1.59/0.61    v1_relat_1(sK2) | ~spl4_3),
% 1.59/0.61    inference(avatar_component_clause,[],[f69])).
% 1.59/0.61  fof(f40,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f20])).
% 1.59/0.61  fof(f20,plain,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f11])).
% 1.59/0.61  fof(f11,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.59/0.61  fof(f41,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f21])).
% 1.59/0.61  fof(f21,plain,(
% 1.59/0.61    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f12])).
% 1.59/0.61  fof(f12,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).
% 1.59/0.61  fof(f710,plain,(
% 1.59/0.61    spl4_48 | ~spl4_42 | ~spl4_45),
% 1.59/0.61    inference(avatar_split_clause,[],[f702,f673,f647,f707])).
% 1.59/0.61  fof(f707,plain,(
% 1.59/0.61    spl4_48 <=> k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 1.59/0.61  fof(f647,plain,(
% 1.59/0.61    spl4_42 <=> v1_relat_1(k2_wellord1(sK2,sK0))),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.59/0.61  fof(f673,plain,(
% 1.59/0.61    spl4_45 <=> r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.59/0.61  fof(f702,plain,(
% 1.59/0.61    ~v1_relat_1(k2_wellord1(sK2,sK0)) | k2_wellord1(sK2,sK0) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) | ~spl4_45),
% 1.59/0.61    inference(resolution,[],[f675,f43])).
% 1.59/0.61  fof(f43,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 1.59/0.61    inference(cnf_transformation,[],[f25])).
% 1.59/0.61  fof(f25,plain,(
% 1.59/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(flattening,[],[f24])).
% 1.59/0.61  fof(f24,plain,(
% 1.59/0.61    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f10])).
% 1.59/0.61  fof(f10,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.59/0.61  fof(f675,plain,(
% 1.59/0.61    r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~spl4_45),
% 1.59/0.61    inference(avatar_component_clause,[],[f673])).
% 1.59/0.61  fof(f683,plain,(
% 1.59/0.61    ~spl4_3 | spl4_42),
% 1.59/0.61    inference(avatar_contradiction_clause,[],[f682])).
% 1.59/0.61  fof(f682,plain,(
% 1.59/0.61    $false | (~spl4_3 | spl4_42)),
% 1.59/0.61    inference(resolution,[],[f649,f73])).
% 1.59/0.61  fof(f649,plain,(
% 1.59/0.61    ~v1_relat_1(k2_wellord1(sK2,sK0)) | spl4_42),
% 1.59/0.61    inference(avatar_component_clause,[],[f647])).
% 1.59/0.61  fof(f676,plain,(
% 1.59/0.61    spl4_45 | ~spl4_3 | ~spl4_24),
% 1.59/0.61    inference(avatar_split_clause,[],[f660,f377,f69,f673])).
% 1.59/0.61  fof(f377,plain,(
% 1.59/0.61    spl4_24 <=> r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.59/0.61  fof(f660,plain,(
% 1.59/0.61    r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_3 | ~spl4_24)),
% 1.59/0.61    inference(resolution,[],[f473,f379])).
% 1.59/0.61  fof(f379,plain,(
% 1.59/0.61    r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~spl4_24),
% 1.59/0.61    inference(avatar_component_clause,[],[f377])).
% 1.59/0.61  fof(f473,plain,(
% 1.59/0.61    ( ! [X4,X5] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,X4)),X5) | r1_tarski(k1_relat_1(k2_wellord1(sK2,X4)),X5)) ) | ~spl4_3),
% 1.59/0.61    inference(superposition,[],[f57,f177])).
% 1.59/0.61  fof(f177,plain,(
% 1.59/0.61    ( ! [X0] : (k3_relat_1(k2_wellord1(sK2,X0)) = k3_tarski(k2_enumset1(k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k1_relat_1(k2_wellord1(sK2,X0)),k2_relat_1(k2_wellord1(sK2,X0))))) ) | ~spl4_3),
% 1.59/0.61    inference(resolution,[],[f55,f73])).
% 1.59/0.61  fof(f55,plain,(
% 1.59/0.61    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f36,f54])).
% 1.59/0.61  fof(f54,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f38,f53])).
% 1.59/0.61  fof(f53,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f39,f47])).
% 1.59/0.61  fof(f47,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f6])).
% 1.59/0.61  fof(f6,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.59/0.61  fof(f39,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f5])).
% 1.59/0.61  fof(f5,axiom,(
% 1.59/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.61  fof(f38,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f7])).
% 1.59/0.61  fof(f7,axiom,(
% 1.59/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.59/0.61  fof(f36,plain,(
% 1.59/0.61    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f19])).
% 1.59/0.61  fof(f19,plain,(
% 1.59/0.61    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.59/0.61    inference(ennf_transformation,[],[f8])).
% 1.59/0.61  fof(f8,axiom,(
% 1.59/0.61    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.59/0.61  fof(f57,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f51,f54])).
% 1.59/0.61  fof(f51,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f30])).
% 1.59/0.61  fof(f30,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.59/0.61    inference(ennf_transformation,[],[f2])).
% 1.59/0.61  fof(f2,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.59/0.61  fof(f650,plain,(
% 1.59/0.61    spl4_41 | ~spl4_42 | ~spl4_38),
% 1.59/0.61    inference(avatar_split_clause,[],[f638,f618,f647,f643])).
% 1.59/0.61  fof(f618,plain,(
% 1.59/0.61    spl4_38 <=> r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.59/0.61  fof(f638,plain,(
% 1.59/0.61    ~v1_relat_1(k2_wellord1(sK2,sK0)) | k2_wellord1(sK2,sK0) = k8_relat_1(sK1,k2_wellord1(sK2,sK0)) | ~spl4_38),
% 1.59/0.61    inference(resolution,[],[f620,f42])).
% 1.59/0.61  fof(f42,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 1.59/0.61    inference(cnf_transformation,[],[f23])).
% 1.59/0.61  fof(f23,plain,(
% 1.59/0.61    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(flattening,[],[f22])).
% 1.59/0.61  fof(f22,plain,(
% 1.59/0.61    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f9])).
% 1.59/0.61  fof(f9,axiom,(
% 1.59/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.59/0.61  fof(f620,plain,(
% 1.59/0.61    r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | ~spl4_38),
% 1.59/0.61    inference(avatar_component_clause,[],[f618])).
% 1.59/0.61  fof(f621,plain,(
% 1.59/0.61    spl4_38 | ~spl4_3 | ~spl4_24),
% 1.59/0.61    inference(avatar_split_clause,[],[f605,f377,f69,f618])).
% 1.59/0.61  fof(f605,plain,(
% 1.59/0.61    r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_3 | ~spl4_24)),
% 1.59/0.61    inference(resolution,[],[f470,f379])).
% 1.59/0.61  fof(f470,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1) | r1_tarski(k2_relat_1(k2_wellord1(sK2,X0)),X1)) ) | ~spl4_3),
% 1.59/0.61    inference(superposition,[],[f147,f177])).
% 1.59/0.61  fof(f147,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_enumset1(X1,X1,X1,X0)),X2) | r1_tarski(X0,X2)) )),
% 1.59/0.61    inference(superposition,[],[f57,f56])).
% 1.59/0.61  fof(f56,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.59/0.61    inference(definition_unfolding,[],[f37,f53,f53])).
% 1.59/0.61  fof(f37,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f4])).
% 1.59/0.61  fof(f4,axiom,(
% 1.59/0.61    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.59/0.61  fof(f380,plain,(
% 1.59/0.61    spl4_24 | ~spl4_2 | ~spl4_3),
% 1.59/0.61    inference(avatar_split_clause,[],[f357,f69,f64,f377])).
% 1.59/0.61  fof(f64,plain,(
% 1.59/0.61    spl4_2 <=> r1_tarski(sK0,sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.59/0.61  fof(f357,plain,(
% 1.59/0.61    r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) | (~spl4_2 | ~spl4_3)),
% 1.59/0.61    inference(resolution,[],[f320,f66])).
% 1.59/0.61  fof(f66,plain,(
% 1.59/0.61    r1_tarski(sK0,sK1) | ~spl4_2),
% 1.59/0.61    inference(avatar_component_clause,[],[f64])).
% 1.59/0.61  fof(f320,plain,(
% 1.59/0.61    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X2)),X3)) ) | ~spl4_3),
% 1.59/0.61    inference(resolution,[],[f318,f52])).
% 1.59/0.61  fof(f52,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f32])).
% 1.59/0.61  fof(f32,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.59/0.61    inference(flattening,[],[f31])).
% 1.59/0.61  fof(f31,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.59/0.61    inference(ennf_transformation,[],[f3])).
% 1.59/0.61  fof(f3,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.59/0.61  fof(f318,plain,(
% 1.59/0.61    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)) ) | ~spl4_3),
% 1.59/0.61    inference(duplicate_literal_removal,[],[f312])).
% 1.59/0.61  fof(f312,plain,(
% 1.59/0.61    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X0)) ) | ~spl4_3),
% 1.59/0.61    inference(resolution,[],[f265,f46])).
% 1.59/0.61  fof(f46,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f26])).
% 1.59/0.61  fof(f26,plain,(
% 1.59/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f1])).
% 1.59/0.61  fof(f1,axiom,(
% 1.59/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.59/0.61  fof(f265,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r2_hidden(sK3(k3_relat_1(k2_wellord1(sK2,X0)),X1),X0) | r1_tarski(k3_relat_1(k2_wellord1(sK2,X0)),X1)) ) | ~spl4_3),
% 1.59/0.61    inference(resolution,[],[f117,f71])).
% 1.59/0.61  fof(f117,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(k3_relat_1(k2_wellord1(X0,X1)),X2),X1) | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2)) )),
% 1.59/0.61    inference(resolution,[],[f50,f45])).
% 1.59/0.61  fof(f45,plain,(
% 1.59/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f26])).
% 1.59/0.61  fof(f50,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2) | r2_hidden(X0,X1)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f29])).
% 1.59/0.61  fof(f29,plain,(
% 1.59/0.61    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 1.59/0.61    inference(flattening,[],[f28])).
% 1.59/0.61  fof(f28,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.59/0.61    inference(ennf_transformation,[],[f13])).
% 1.59/0.61  fof(f13,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).
% 1.59/0.61  fof(f219,plain,(
% 1.59/0.61    ~spl4_14 | spl4_1 | ~spl4_3),
% 1.59/0.61    inference(avatar_split_clause,[],[f211,f69,f59,f215])).
% 1.59/0.61  fof(f215,plain,(
% 1.59/0.61    spl4_14 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK0),sK1)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.59/0.61  fof(f59,plain,(
% 1.59/0.61    spl4_1 <=> k2_wellord1(sK2,sK0) = k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.59/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.59/0.61  fof(f211,plain,(
% 1.59/0.61    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) | (spl4_1 | ~spl4_3)),
% 1.59/0.61    inference(superposition,[],[f61,f166])).
% 1.59/0.61  fof(f166,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k2_wellord1(k2_wellord1(sK2,X0),X1) = k2_wellord1(k2_wellord1(sK2,X1),X0)) ) | ~spl4_3),
% 1.59/0.61    inference(resolution,[],[f48,f71])).
% 1.59/0.61  fof(f48,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f27])).
% 1.59/0.61  fof(f27,plain,(
% 1.59/0.61    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 1.59/0.61    inference(ennf_transformation,[],[f14])).
% 1.59/0.61  fof(f14,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).
% 1.59/0.61  fof(f61,plain,(
% 1.59/0.61    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) | spl4_1),
% 1.59/0.61    inference(avatar_component_clause,[],[f59])).
% 1.59/0.61  fof(f72,plain,(
% 1.59/0.61    spl4_3),
% 1.59/0.61    inference(avatar_split_clause,[],[f33,f69])).
% 1.59/0.61  fof(f33,plain,(
% 1.59/0.61    v1_relat_1(sK2)),
% 1.59/0.61    inference(cnf_transformation,[],[f18])).
% 1.59/0.61  fof(f18,plain,(
% 1.59/0.61    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.59/0.61    inference(flattening,[],[f17])).
% 1.59/0.61  fof(f17,plain,(
% 1.59/0.61    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.59/0.61    inference(ennf_transformation,[],[f16])).
% 1.59/0.61  fof(f16,negated_conjecture,(
% 1.59/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.59/0.61    inference(negated_conjecture,[],[f15])).
% 1.59/0.61  fof(f15,conjecture,(
% 1.59/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).
% 1.59/0.61  fof(f67,plain,(
% 1.59/0.61    spl4_2),
% 1.59/0.61    inference(avatar_split_clause,[],[f34,f64])).
% 1.59/0.61  fof(f34,plain,(
% 1.59/0.61    r1_tarski(sK0,sK1)),
% 1.59/0.61    inference(cnf_transformation,[],[f18])).
% 1.59/0.61  fof(f62,plain,(
% 1.59/0.61    ~spl4_1),
% 1.59/0.61    inference(avatar_split_clause,[],[f35,f59])).
% 1.59/0.61  fof(f35,plain,(
% 1.59/0.61    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 1.59/0.61    inference(cnf_transformation,[],[f18])).
% 1.59/0.61  % SZS output end Proof for theBenchmark
% 1.59/0.61  % (23646)------------------------------
% 1.59/0.61  % (23646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (23646)Termination reason: Refutation
% 1.59/0.61  
% 1.59/0.61  % (23646)Memory used [KB]: 11769
% 1.59/0.61  % (23646)Time elapsed: 0.205 s
% 1.59/0.61  % (23646)------------------------------
% 1.59/0.61  % (23646)------------------------------
% 2.05/0.63  % (23622)Success in time 0.266 s
%------------------------------------------------------------------------------
