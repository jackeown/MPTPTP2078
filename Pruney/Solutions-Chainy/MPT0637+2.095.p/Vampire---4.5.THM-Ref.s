%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 139 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  201 ( 301 expanded)
%              Number of equality atoms :   65 ( 103 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f58,f64,f68,f75,f79,f83,f90,f95,f100])).

fof(f100,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | spl2_8
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | spl2_8
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f74,f98])).

fof(f98,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f97,f63])).

fof(f63,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_6
  <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f97,plain,
    ( ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_11
    | ~ spl2_12 ),
    inference(backward_demodulation,[],[f91,f96])).

fof(f96,plain,
    ( ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))
    | ~ spl2_1
    | ~ spl2_12 ),
    inference(resolution,[],[f94,f41])).

fof(f41,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f94,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl2_12
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f91,plain,
    ( ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(resolution,[],[f89,f57])).

fof(f57,plain,
    ( ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_5
  <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f74,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_8
  <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f95,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f38,f93])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f90,plain,
    ( spl2_11
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f86,f81,f77,f48,f40,f88])).

fof(f48,plain,
    ( spl2_3
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f77,plain,
    ( spl2_9
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f81,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f85,f78])).

fof(f78,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f84,f49])).

fof(f49,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) )
    | ~ spl2_1
    | ~ spl2_10 ),
    inference(resolution,[],[f82,f41])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f83,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f81])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f79,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f69,f66,f40,f77])).

fof(f66,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f69,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f67,f41])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,
    ( ~ spl2_8
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f70,f66,f40,f72])).

fof(f70,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f36,f69])).

fof(f36,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f22,f35])).

fof(f22,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f68,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f64,plain,
    ( spl2_6
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f60,f52,f44,f40,f62])).

fof(f44,plain,
    ( spl2_2
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k7_relat_1(X0,k1_relat_1(X0)) = X0
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f60,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f59,f45])).

fof(f45,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f59,plain,
    ( ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))
    | ~ spl2_1
    | ~ spl2_4 ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,k1_relat_1(X0)) = X0 )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f58,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f37,f56])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f54,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f50,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f46,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f24,f44])).

fof(f24,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (20513)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (20511)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (20518)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (20522)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (20521)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (20518)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (20516)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (20523)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (20522)Refutation not found, incomplete strategy% (20522)------------------------------
% 0.21/0.47  % (20522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20522)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (20522)Memory used [KB]: 10490
% 0.21/0.47  % (20522)Time elapsed: 0.045 s
% 0.21/0.47  % (20522)------------------------------
% 0.21/0.47  % (20522)------------------------------
% 0.21/0.47  % (20514)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (20517)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (20515)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f58,f64,f68,f75,f79,f83,f90,f95,f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ~spl2_1 | ~spl2_5 | ~spl2_6 | spl2_8 | ~spl2_11 | ~spl2_12),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    $false | (~spl2_1 | ~spl2_5 | ~spl2_6 | spl2_8 | ~spl2_11 | ~spl2_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) ) | (~spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_11 | ~spl2_12)),
% 0.21/0.47    inference(forward_demodulation,[],[f97,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl2_6 <=> ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)) ) | (~spl2_1 | ~spl2_5 | ~spl2_11 | ~spl2_12)),
% 0.21/0.47    inference(backward_demodulation,[],[f91,f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) ) | (~spl2_1 | ~spl2_12)),
% 0.21/0.47    inference(resolution,[],[f94,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    spl2_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) ) | ~spl2_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    spl2_12 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) ) | (~spl2_5 | ~spl2_11)),
% 0.21/0.47    inference(resolution,[],[f89,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) ) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl2_5 <=> ! [X1,X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) ) | ~spl2_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl2_11 <=> ! [X1,X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl2_8 <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl2_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f93])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f33,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f28,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f29,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl2_11 | ~spl2_1 | ~spl2_3 | ~spl2_9 | ~spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f81,f77,f48,f40,f88])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl2_3 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl2_9 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl2_10 <=> ! [X1,X0] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) | ~r1_tarski(X0,X1)) ) | (~spl2_1 | ~spl2_3 | ~spl2_9 | ~spl2_10)),
% 0.21/0.47    inference(forward_demodulation,[],[f85,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_3 | ~spl2_10)),
% 0.21/0.47    inference(forward_demodulation,[],[f84,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f48])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ) | (~spl2_1 | ~spl2_10)),
% 0.21/0.47    inference(resolution,[],[f82,f41])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) ) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f81])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl2_9 | ~spl2_1 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f69,f66,f40,f77])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl2_7 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_1 | ~spl2_7)),
% 0.21/0.47    inference(resolution,[],[f67,f41])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ~spl2_8 | ~spl2_1 | ~spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f70,f66,f40,f72])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_1 | ~spl2_7)),
% 0.21/0.47    inference(backward_demodulation,[],[f36,f69])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.47    inference(definition_unfolding,[],[f22,f35])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f11])).
% 0.21/0.47  fof(f11,conjecture,(
% 0.21/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f66])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl2_6 | ~spl2_1 | ~spl2_2 | ~spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f52,f44,f40,f62])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl2_2 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl2_4 <=> ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) ) | (~spl2_1 | ~spl2_2 | ~spl2_4)),
% 0.21/0.47    inference(forward_demodulation,[],[f59,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) ) | (~spl2_1 | ~spl2_4)),
% 0.21/0.47    inference(resolution,[],[f53,f41])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f56])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f27,f35])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f52])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f48])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f44])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f40])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (20518)------------------------------
% 0.21/0.47  % (20518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20518)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (20518)Memory used [KB]: 6140
% 0.21/0.47  % (20518)Time elapsed: 0.006 s
% 0.21/0.47  % (20518)------------------------------
% 0.21/0.47  % (20518)------------------------------
% 0.21/0.48  % (20510)Success in time 0.122 s
%------------------------------------------------------------------------------
