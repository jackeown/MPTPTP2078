%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:54 EST 2020

% Result     : Theorem 2.95s
% Output     : Refutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 210 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  215 ( 431 expanded)
%              Number of equality atoms :   74 ( 169 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f120,f122,f1364,f2327,f2329,f2457,f2471])).

fof(f2471,plain,(
    ~ spl6_47 ),
    inference(avatar_contradiction_clause,[],[f2465])).

fof(f2465,plain,
    ( $false
    | ~ spl6_47 ),
    inference(resolution,[],[f2443,f900])).

fof(f900,plain,(
    ! [X14] : ~ r2_hidden(X14,k1_xboole_0) ),
    inference(global_subsumption,[],[f316,f323])).

fof(f323,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k1_xboole_0)
      | r2_hidden(X6,X5) ) ),
    inference(superposition,[],[f75,f304])).

fof(f304,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5) ),
    inference(resolution,[],[f292,f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f153,f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f153,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f94,f95])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) ),
    inference(resolution,[],[f79,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_setfam_1(X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_setfam_1(X0) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_setfam_1(X0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f79,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f94,plain,(
    ! [X2,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2) ),
    inference(resolution,[],[f77,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f77,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_enumset1(X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f292,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X0),X1)
      | r1_tarski(k4_xboole_0(X0,X0),X1) ) ),
    inference(resolution,[],[f102,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f74,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f75,f35])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f316,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k1_xboole_0)
      | ~ r2_hidden(X8,X7) ) ),
    inference(superposition,[],[f74,f295])).

fof(f295,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5) ),
    inference(resolution,[],[f291,f155])).

fof(f291,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),X2)
      | r1_tarski(k4_xboole_0(X2,X3),X2) ) ),
    inference(resolution,[],[f102,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2443,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f2441])).

fof(f2441,plain,
    ( spl6_47
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f2457,plain,
    ( spl6_47
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f2379,f1007,f2441])).

fof(f1007,plain,
    ( spl6_15
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f2379,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl6_15 ),
    inference(superposition,[],[f79,f1009])).

fof(f1009,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f2329,plain,(
    spl6_42 ),
    inference(avatar_contradiction_clause,[],[f2328])).

fof(f2328,plain,
    ( $false
    | spl6_42 ),
    inference(resolution,[],[f2326,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2326,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_42 ),
    inference(avatar_component_clause,[],[f2324])).

fof(f2324,plain,
    ( spl6_42
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f2327,plain,
    ( spl6_4
    | spl6_15
    | ~ spl6_42
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f2317,f1003,f2324,f1007,f116])).

fof(f116,plain,
    ( spl6_4
  <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1003,plain,
    ( spl6_14
  <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f2317,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | ~ spl6_14 ),
    inference(superposition,[],[f30,f1005])).

fof(f1005,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f1003])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK1(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f1364,plain,
    ( spl6_15
    | spl6_14
    | spl6_4 ),
    inference(avatar_split_clause,[],[f1363,f116,f1003,f1007])).

fof(f1363,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl6_4 ),
    inference(duplicate_literal_removal,[],[f1354])).

fof(f1354,plain,
    ( sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)
    | spl6_4 ),
    inference(resolution,[],[f176,f118])).

fof(f118,plain,
    ( ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f176,plain,(
    ! [X10,X8,X9] :
      ( r1_tarski(X10,k1_setfam_1(k2_enumset1(X9,X9,X9,X8)))
      | sK1(k2_enumset1(X9,X9,X9,X8),X10) = X9
      | k1_xboole_0 = k2_enumset1(X9,X9,X9,X8)
      | sK1(k2_enumset1(X9,X9,X9,X8),X10) = X8 ) ),
    inference(resolution,[],[f80,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f122,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl6_3 ),
    inference(resolution,[],[f114,f87])).

fof(f87,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(resolution,[],[f72,f28])).

fof(f72,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f54])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f114,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_3
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f120,plain,
    ( ~ spl6_4
    | ~ spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f107,f82,f112,f116])).

fof(f82,plain,
    ( spl6_1
  <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f107,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)
    | ~ r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl6_1 ),
    inference(extensionality_resolution,[],[f33,f84])).

fof(f84,plain,
    ( sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f56,f82])).

fof(f56,plain,(
    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f22,f55])).

fof(f22,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (11151)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (11143)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (11130)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (11135)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (11132)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (11133)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (11128)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (11128)Refutation not found, incomplete strategy% (11128)------------------------------
% 0.22/0.53  % (11128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11128)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11128)Memory used [KB]: 1663
% 0.22/0.53  % (11128)Time elapsed: 0.115 s
% 0.22/0.53  % (11128)------------------------------
% 0.22/0.53  % (11128)------------------------------
% 0.22/0.53  % (11157)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (11134)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (11129)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (11130)Refutation not found, incomplete strategy% (11130)------------------------------
% 0.22/0.53  % (11130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11130)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11130)Memory used [KB]: 10618
% 0.22/0.53  % (11130)Time elapsed: 0.126 s
% 0.22/0.53  % (11130)------------------------------
% 0.22/0.53  % (11130)------------------------------
% 1.41/0.54  % (11146)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.54  % (11153)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.54  % (11141)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.54  % (11156)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (11145)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.54  % (11155)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (11136)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (11150)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.55  % (11136)Refutation not found, incomplete strategy% (11136)------------------------------
% 1.41/0.55  % (11136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (11136)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (11136)Memory used [KB]: 10618
% 1.41/0.55  % (11136)Time elapsed: 0.139 s
% 1.41/0.55  % (11136)------------------------------
% 1.41/0.55  % (11136)------------------------------
% 1.41/0.55  % (11148)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (11147)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (11138)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (11148)Refutation not found, incomplete strategy% (11148)------------------------------
% 1.41/0.55  % (11148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (11148)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (11148)Memory used [KB]: 10746
% 1.41/0.55  % (11148)Time elapsed: 0.139 s
% 1.41/0.55  % (11148)------------------------------
% 1.41/0.55  % (11148)------------------------------
% 1.41/0.55  % (11138)Refutation not found, incomplete strategy% (11138)------------------------------
% 1.41/0.55  % (11138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (11138)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (11138)Memory used [KB]: 10618
% 1.41/0.55  % (11138)Time elapsed: 0.140 s
% 1.41/0.55  % (11138)------------------------------
% 1.41/0.55  % (11138)------------------------------
% 1.50/0.55  % (11140)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.50/0.55  % (11144)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.50/0.55  % (11137)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (11142)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.56  % (11152)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.57  % (11131)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.50/0.57  % (11154)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.59  % (11139)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.59  % (11149)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.59  % (11149)Refutation not found, incomplete strategy% (11149)------------------------------
% 1.50/0.59  % (11149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (11139)Refutation not found, incomplete strategy% (11139)------------------------------
% 1.50/0.60  % (11139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (11149)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.60  
% 1.50/0.60  % (11149)Memory used [KB]: 1663
% 1.50/0.60  % (11149)Time elapsed: 0.151 s
% 1.50/0.60  % (11149)------------------------------
% 1.50/0.60  % (11149)------------------------------
% 1.50/0.60  % (11139)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.60  
% 1.50/0.60  % (11139)Memory used [KB]: 10746
% 1.50/0.60  % (11139)Time elapsed: 0.156 s
% 1.50/0.60  % (11139)------------------------------
% 1.50/0.60  % (11139)------------------------------
% 2.28/0.73  % (11189)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.28/0.73  % (11190)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.28/0.74  % (11186)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.71/0.75  % (11161)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.71/0.75  % (11161)Refutation not found, incomplete strategy% (11161)------------------------------
% 2.71/0.75  % (11161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.75  % (11161)Termination reason: Refutation not found, incomplete strategy
% 2.71/0.75  
% 2.71/0.75  % (11161)Memory used [KB]: 6268
% 2.71/0.75  % (11161)Time elapsed: 0.167 s
% 2.71/0.75  % (11161)------------------------------
% 2.71/0.75  % (11161)------------------------------
% 2.71/0.75  % (11162)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.95/0.79  % (11170)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.95/0.80  % (11144)Refutation found. Thanks to Tanya!
% 2.95/0.80  % SZS status Theorem for theBenchmark
% 2.95/0.80  % (11171)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.95/0.80  % (11133)Time limit reached!
% 2.95/0.80  % (11133)------------------------------
% 2.95/0.80  % (11133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.80  % (11133)Termination reason: Time limit
% 2.95/0.80  % (11133)Termination phase: Saturation
% 2.95/0.80  
% 2.95/0.80  % (11133)Memory used [KB]: 7419
% 2.95/0.80  % (11133)Time elapsed: 0.400 s
% 2.95/0.80  % (11133)------------------------------
% 2.95/0.80  % (11133)------------------------------
% 2.95/0.82  % SZS output start Proof for theBenchmark
% 2.95/0.82  fof(f2474,plain,(
% 2.95/0.82    $false),
% 2.95/0.82    inference(avatar_sat_refutation,[],[f85,f120,f122,f1364,f2327,f2329,f2457,f2471])).
% 2.95/0.82  fof(f2471,plain,(
% 2.95/0.82    ~spl6_47),
% 2.95/0.82    inference(avatar_contradiction_clause,[],[f2465])).
% 2.95/0.82  fof(f2465,plain,(
% 2.95/0.82    $false | ~spl6_47),
% 2.95/0.82    inference(resolution,[],[f2443,f900])).
% 2.95/0.82  fof(f900,plain,(
% 2.95/0.82    ( ! [X14] : (~r2_hidden(X14,k1_xboole_0)) )),
% 2.95/0.82    inference(global_subsumption,[],[f316,f323])).
% 2.95/0.82  fof(f323,plain,(
% 2.95/0.82    ( ! [X6,X5] : (~r2_hidden(X6,k1_xboole_0) | r2_hidden(X6,X5)) )),
% 2.95/0.82    inference(superposition,[],[f75,f304])).
% 2.95/0.82  fof(f304,plain,(
% 2.95/0.82    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) )),
% 2.95/0.82    inference(resolution,[],[f292,f155])).
% 2.95/0.82  fof(f155,plain,(
% 2.95/0.82    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.95/0.82    inference(resolution,[],[f153,f33])).
% 2.95/0.82  fof(f33,plain,(
% 2.95/0.82    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.95/0.82    inference(cnf_transformation,[],[f3])).
% 2.95/0.82  fof(f3,axiom,(
% 2.95/0.82    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.95/0.82  fof(f153,plain,(
% 2.95/0.82    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.95/0.82    inference(superposition,[],[f94,f95])).
% 2.95/0.82  fof(f95,plain,(
% 2.95/0.82    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) )),
% 2.95/0.82    inference(resolution,[],[f79,f26])).
% 2.95/0.82  fof(f26,plain,(
% 2.95/0.82    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_setfam_1(X0) = k1_xboole_0) )),
% 2.95/0.82    inference(cnf_transformation,[],[f17])).
% 2.95/0.82  fof(f17,plain,(
% 2.95/0.82    ! [X0] : (k1_setfam_1(X0) = k1_xboole_0 | ~r2_hidden(k1_xboole_0,X0))),
% 2.95/0.82    inference(ennf_transformation,[],[f12])).
% 2.95/0.82  fof(f12,axiom,(
% 2.95/0.82    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_setfam_1(X0) = k1_xboole_0)),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_setfam_1)).
% 2.95/0.82  fof(f79,plain,(
% 2.95/0.82    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 2.95/0.82    inference(equality_resolution,[],[f78])).
% 2.95/0.82  fof(f78,plain,(
% 2.95/0.82    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 2.95/0.82    inference(equality_resolution,[],[f63])).
% 2.95/0.82  fof(f63,plain,(
% 2.95/0.82    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.95/0.82    inference(definition_unfolding,[],[f52,f54])).
% 2.95/0.82  fof(f54,plain,(
% 2.95/0.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.95/0.82    inference(definition_unfolding,[],[f27,f41])).
% 2.95/0.82  fof(f41,plain,(
% 2.95/0.82    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.95/0.82    inference(cnf_transformation,[],[f8])).
% 2.95/0.82  fof(f8,axiom,(
% 2.95/0.82    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.95/0.82  fof(f27,plain,(
% 2.95/0.82    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.95/0.82    inference(cnf_transformation,[],[f7])).
% 2.95/0.82  fof(f7,axiom,(
% 2.95/0.82    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.95/0.82  fof(f52,plain,(
% 2.95/0.82    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.95/0.82    inference(cnf_transformation,[],[f5])).
% 2.95/0.82  fof(f5,axiom,(
% 2.95/0.82    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 2.95/0.82  fof(f94,plain,(
% 2.95/0.82    ( ! [X2,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)),X2)) )),
% 2.95/0.82    inference(resolution,[],[f77,f28])).
% 2.95/0.82  fof(f28,plain,(
% 2.95/0.82    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_setfam_1(X1),X0)) )),
% 2.95/0.82    inference(cnf_transformation,[],[f18])).
% 2.95/0.82  fof(f18,plain,(
% 2.95/0.82    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 2.95/0.82    inference(ennf_transformation,[],[f11])).
% 2.95/0.82  fof(f11,axiom,(
% 2.95/0.82    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 2.95/0.82  fof(f77,plain,(
% 2.95/0.82    ( ! [X0,X3] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X3))) )),
% 2.95/0.82    inference(equality_resolution,[],[f76])).
% 2.95/0.82  fof(f76,plain,(
% 2.95/0.82    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X3) != X2) )),
% 2.95/0.82    inference(equality_resolution,[],[f62])).
% 2.95/0.82  fof(f62,plain,(
% 2.95/0.82    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.95/0.82    inference(definition_unfolding,[],[f53,f54])).
% 2.95/0.82  fof(f53,plain,(
% 2.95/0.82    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.95/0.82    inference(cnf_transformation,[],[f5])).
% 2.95/0.82  fof(f292,plain,(
% 2.95/0.82    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 2.95/0.82    inference(duplicate_literal_removal,[],[f282])).
% 2.95/0.82  fof(f282,plain,(
% 2.95/0.82    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1) | r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 2.95/0.82    inference(resolution,[],[f102,f101])).
% 2.95/0.82  fof(f101,plain,(
% 2.95/0.82    ( ! [X2,X0,X1] : (~r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.95/0.82    inference(resolution,[],[f74,f35])).
% 2.95/0.82  fof(f35,plain,(
% 2.95/0.82    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.95/0.82    inference(cnf_transformation,[],[f21])).
% 2.95/0.82  fof(f21,plain,(
% 2.95/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.95/0.82    inference(ennf_transformation,[],[f1])).
% 2.95/0.82  fof(f1,axiom,(
% 2.95/0.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.95/0.82  fof(f74,plain,(
% 2.95/0.82    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 2.95/0.82    inference(equality_resolution,[],[f46])).
% 2.95/0.82  fof(f46,plain,(
% 2.95/0.82    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.95/0.82    inference(cnf_transformation,[],[f2])).
% 2.95/0.82  fof(f2,axiom,(
% 2.95/0.82    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.95/0.82  fof(f102,plain,(
% 2.95/0.82    ( ! [X2,X0,X1] : (r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.95/0.82    inference(resolution,[],[f75,f35])).
% 2.95/0.82  fof(f75,plain,(
% 2.95/0.82    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 2.95/0.82    inference(equality_resolution,[],[f45])).
% 2.95/0.82  fof(f45,plain,(
% 2.95/0.82    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.95/0.82    inference(cnf_transformation,[],[f2])).
% 2.95/0.82  fof(f316,plain,(
% 2.95/0.82    ( ! [X8,X7] : (~r2_hidden(X8,k1_xboole_0) | ~r2_hidden(X8,X7)) )),
% 2.95/0.82    inference(superposition,[],[f74,f295])).
% 2.95/0.82  fof(f295,plain,(
% 2.95/0.82    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X5)) )),
% 2.95/0.82    inference(resolution,[],[f291,f155])).
% 2.95/0.82  fof(f291,plain,(
% 2.95/0.82    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 2.95/0.82    inference(duplicate_literal_removal,[],[f283])).
% 2.95/0.82  fof(f283,plain,(
% 2.95/0.82    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2) | r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 2.95/0.82    inference(resolution,[],[f102,f36])).
% 2.95/0.82  fof(f36,plain,(
% 2.95/0.82    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.95/0.82    inference(cnf_transformation,[],[f21])).
% 2.95/0.82  fof(f2443,plain,(
% 2.95/0.82    r2_hidden(sK0,k1_xboole_0) | ~spl6_47),
% 2.95/0.82    inference(avatar_component_clause,[],[f2441])).
% 2.95/0.82  fof(f2441,plain,(
% 2.95/0.82    spl6_47 <=> r2_hidden(sK0,k1_xboole_0)),
% 2.95/0.82    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 2.95/0.82  fof(f2457,plain,(
% 2.95/0.82    spl6_47 | ~spl6_15),
% 2.95/0.82    inference(avatar_split_clause,[],[f2379,f1007,f2441])).
% 2.95/0.82  fof(f1007,plain,(
% 2.95/0.82    spl6_15 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 2.95/0.82    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 2.95/0.82  fof(f2379,plain,(
% 2.95/0.82    r2_hidden(sK0,k1_xboole_0) | ~spl6_15),
% 2.95/0.82    inference(superposition,[],[f79,f1009])).
% 2.95/0.82  fof(f1009,plain,(
% 2.95/0.82    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_15),
% 2.95/0.82    inference(avatar_component_clause,[],[f1007])).
% 2.95/0.82  fof(f2329,plain,(
% 2.95/0.82    spl6_42),
% 2.95/0.82    inference(avatar_contradiction_clause,[],[f2328])).
% 2.95/0.82  fof(f2328,plain,(
% 2.95/0.82    $false | spl6_42),
% 2.95/0.82    inference(resolution,[],[f2326,f68])).
% 2.95/0.82  fof(f68,plain,(
% 2.95/0.82    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.95/0.82    inference(equality_resolution,[],[f32])).
% 2.95/0.82  fof(f32,plain,(
% 2.95/0.82    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.95/0.82    inference(cnf_transformation,[],[f3])).
% 2.95/0.82  fof(f2326,plain,(
% 2.95/0.82    ~r1_tarski(sK0,sK0) | spl6_42),
% 2.95/0.82    inference(avatar_component_clause,[],[f2324])).
% 2.95/0.82  fof(f2324,plain,(
% 2.95/0.82    spl6_42 <=> r1_tarski(sK0,sK0)),
% 2.95/0.82    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 2.95/0.82  fof(f2327,plain,(
% 2.95/0.82    spl6_4 | spl6_15 | ~spl6_42 | ~spl6_14),
% 2.95/0.82    inference(avatar_split_clause,[],[f2317,f1003,f2324,f1007,f116])).
% 2.95/0.82  fof(f116,plain,(
% 2.95/0.82    spl6_4 <=> r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)))),
% 2.95/0.82    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 2.95/0.82  fof(f1003,plain,(
% 2.95/0.82    spl6_14 <=> sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0)),
% 2.95/0.82    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 2.95/0.82  fof(f2317,plain,(
% 2.95/0.82    ~r1_tarski(sK0,sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | ~spl6_14),
% 2.95/0.82    inference(superposition,[],[f30,f1005])).
% 2.95/0.82  fof(f1005,plain,(
% 2.95/0.82    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | ~spl6_14),
% 2.95/0.82    inference(avatar_component_clause,[],[f1003])).
% 2.95/0.82  fof(f30,plain,(
% 2.95/0.82    ( ! [X0,X1] : (~r1_tarski(X1,sK1(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.95/0.82    inference(cnf_transformation,[],[f20])).
% 2.95/0.82  fof(f20,plain,(
% 2.95/0.82    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.95/0.82    inference(flattening,[],[f19])).
% 2.95/0.82  fof(f19,plain,(
% 2.95/0.82    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 2.95/0.82    inference(ennf_transformation,[],[f13])).
% 2.95/0.82  fof(f13,axiom,(
% 2.95/0.82    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 2.95/0.82  fof(f1364,plain,(
% 2.95/0.82    spl6_15 | spl6_14 | spl6_4),
% 2.95/0.82    inference(avatar_split_clause,[],[f1363,f116,f1003,f1007])).
% 2.95/0.82  fof(f1363,plain,(
% 2.95/0.82    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | spl6_4),
% 2.95/0.82    inference(duplicate_literal_removal,[],[f1354])).
% 2.95/0.82  fof(f1354,plain,(
% 2.95/0.82    sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | sK0 = sK1(k2_enumset1(sK0,sK0,sK0,sK0),sK0) | spl6_4),
% 2.95/0.82    inference(resolution,[],[f176,f118])).
% 2.95/0.82  fof(f118,plain,(
% 2.95/0.82    ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl6_4),
% 2.95/0.82    inference(avatar_component_clause,[],[f116])).
% 2.95/0.82  fof(f176,plain,(
% 2.95/0.82    ( ! [X10,X8,X9] : (r1_tarski(X10,k1_setfam_1(k2_enumset1(X9,X9,X9,X8))) | sK1(k2_enumset1(X9,X9,X9,X8),X10) = X9 | k1_xboole_0 = k2_enumset1(X9,X9,X9,X8) | sK1(k2_enumset1(X9,X9,X9,X8),X10) = X8) )),
% 2.95/0.82    inference(resolution,[],[f80,f29])).
% 2.95/0.82  fof(f29,plain,(
% 2.95/0.82    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 2.95/0.82    inference(cnf_transformation,[],[f20])).
% 2.95/0.82  fof(f80,plain,(
% 2.95/0.82    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 2.95/0.82    inference(equality_resolution,[],[f64])).
% 2.95/0.82  fof(f64,plain,(
% 2.95/0.82    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 2.95/0.82    inference(definition_unfolding,[],[f51,f54])).
% 2.95/0.82  fof(f51,plain,(
% 2.95/0.82    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.95/0.82    inference(cnf_transformation,[],[f5])).
% 2.95/0.82  fof(f122,plain,(
% 2.95/0.82    spl6_3),
% 2.95/0.82    inference(avatar_contradiction_clause,[],[f121])).
% 2.95/0.82  fof(f121,plain,(
% 2.95/0.82    $false | spl6_3),
% 2.95/0.82    inference(resolution,[],[f114,f87])).
% 2.95/0.82  fof(f87,plain,(
% 2.95/0.82    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0)) )),
% 2.95/0.82    inference(resolution,[],[f72,f28])).
% 2.95/0.82  fof(f72,plain,(
% 2.95/0.82    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 2.95/0.82    inference(equality_resolution,[],[f71])).
% 2.95/0.82  fof(f71,plain,(
% 2.95/0.82    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 2.95/0.82    inference(equality_resolution,[],[f61])).
% 2.95/0.82  fof(f61,plain,(
% 2.95/0.82    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.95/0.82    inference(definition_unfolding,[],[f37,f55])).
% 2.95/0.82  fof(f55,plain,(
% 2.95/0.82    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.95/0.82    inference(definition_unfolding,[],[f25,f54])).
% 2.95/0.82  fof(f25,plain,(
% 2.95/0.82    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.95/0.82    inference(cnf_transformation,[],[f6])).
% 2.95/0.82  fof(f6,axiom,(
% 2.95/0.82    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.95/0.82  fof(f37,plain,(
% 2.95/0.82    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.95/0.82    inference(cnf_transformation,[],[f4])).
% 2.95/0.82  fof(f4,axiom,(
% 2.95/0.82    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.95/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 2.95/0.82  fof(f114,plain,(
% 2.95/0.82    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | spl6_3),
% 2.95/0.82    inference(avatar_component_clause,[],[f112])).
% 2.95/0.82  fof(f112,plain,(
% 2.95/0.82    spl6_3 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0)),
% 2.95/0.82    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 2.95/0.82  fof(f120,plain,(
% 2.95/0.82    ~spl6_4 | ~spl6_3 | spl6_1),
% 2.95/0.82    inference(avatar_split_clause,[],[f107,f82,f112,f116])).
% 2.95/0.82  fof(f82,plain,(
% 2.95/0.82    spl6_1 <=> sK0 = k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.95/0.82    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.95/0.82  fof(f107,plain,(
% 2.95/0.82    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)),sK0) | ~r1_tarski(sK0,k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))) | spl6_1),
% 2.95/0.82    inference(extensionality_resolution,[],[f33,f84])).
% 2.95/0.82  fof(f84,plain,(
% 2.95/0.82    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0)) | spl6_1),
% 2.95/0.82    inference(avatar_component_clause,[],[f82])).
% 2.95/0.82  fof(f85,plain,(
% 2.95/0.82    ~spl6_1),
% 2.95/0.82    inference(avatar_split_clause,[],[f56,f82])).
% 2.95/0.82  fof(f56,plain,(
% 2.95/0.82    sK0 != k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.95/0.82    inference(definition_unfolding,[],[f22,f55])).
% 3.28/0.82  fof(f22,plain,(
% 3.28/0.82    sK0 != k1_setfam_1(k1_tarski(sK0))),
% 3.28/0.82    inference(cnf_transformation,[],[f16])).
% 3.28/0.82  fof(f16,plain,(
% 3.28/0.82    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 3.28/0.82    inference(ennf_transformation,[],[f15])).
% 3.28/0.82  fof(f15,negated_conjecture,(
% 3.28/0.82    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.28/0.82    inference(negated_conjecture,[],[f14])).
% 3.28/0.82  fof(f14,conjecture,(
% 3.28/0.82    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 3.28/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 3.28/0.82  % SZS output end Proof for theBenchmark
% 3.28/0.82  % (11144)------------------------------
% 3.28/0.82  % (11144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.82  % (11144)Termination reason: Refutation
% 3.28/0.82  
% 3.28/0.82  % (11144)Memory used [KB]: 13304
% 3.28/0.82  % (11144)Time elapsed: 0.377 s
% 3.28/0.82  % (11144)------------------------------
% 3.28/0.82  % (11144)------------------------------
% 3.28/0.83  % (11127)Success in time 0.461 s
%------------------------------------------------------------------------------
