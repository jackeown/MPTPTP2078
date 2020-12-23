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
% DateTime   : Thu Dec  3 12:31:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 164 expanded)
%              Number of leaves         :   30 (  79 expanded)
%              Depth                    :    6
%              Number of atoms          :  279 ( 435 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f512,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f46,f54,f58,f62,f68,f73,f94,f133,f137,f156,f192,f211,f226,f257,f265,f349,f477,f505,f511])).

fof(f511,plain,
    ( spl3_2
    | ~ spl3_19
    | ~ spl3_66 ),
    inference(avatar_contradiction_clause,[],[f510])).

fof(f510,plain,
    ( $false
    | spl3_2
    | ~ spl3_19
    | ~ spl3_66 ),
    inference(subsumption_resolution,[],[f41,f506])).

fof(f506,plain,
    ( ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,sK1))
    | ~ spl3_19
    | ~ spl3_66 ),
    inference(resolution,[],[f504,f132])).

fof(f132,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        | r1_xboole_0(X1,k4_xboole_0(X0,X2)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f504,plain,
    ( ! [X0] : r1_xboole_0(X0,k4_xboole_0(sK0,sK1))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl3_66
  <=> ! [X0] : r1_xboole_0(X0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f41,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f505,plain,
    ( spl3_66
    | ~ spl3_3
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f485,f475,f44,f503])).

fof(f44,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f475,plain,
    ( spl3_64
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,k4_xboole_0(sK0,sK1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f485,plain,
    ( ! [X0] : r1_xboole_0(X0,k4_xboole_0(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_64 ),
    inference(resolution,[],[f476,f45])).

fof(f45,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_xboole_0(X0,k4_xboole_0(sK0,sK1)) )
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f475])).

fof(f477,plain,
    ( spl3_64
    | ~ spl3_37
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f468,f347,f263,f475])).

fof(f263,plain,
    ( spl3_37
  <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f347,plain,
    ( spl3_48
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(X2,X3)))
        | ~ r1_tarski(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f468,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(sK0,sK1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_37
    | ~ spl3_48 ),
    inference(resolution,[],[f348,f264])).

fof(f264,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,sK1),X0)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f263])).

fof(f348,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(X2,X3)))
        | r1_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X2) )
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f347])).

fof(f349,plain,
    ( spl3_48
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f184,f154,f92,f347])).

fof(f92,plain,
    ( spl3_13
  <=> ! [X1,X0] : r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f154,plain,
    ( spl3_23
  <=> ! [X1,X3,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X3)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f184,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_xboole_0(X0,X1)
        | ~ r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(X2,X3)))
        | ~ r1_tarski(X0,X2) )
    | ~ spl3_13
    | ~ spl3_23 ),
    inference(resolution,[],[f155,f93])).

fof(f93,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f155,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_xboole_0(X1,X3)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X2,X3)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f154])).

fof(f265,plain,
    ( spl3_37
    | ~ spl3_28
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f258,f255,f190,f263])).

fof(f190,plain,
    ( spl3_28
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f255,plain,
    ( spl3_36
  <=> ! [X22,X21] : r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X21,X22)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f258,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,sK1),X0)
    | ~ spl3_28
    | ~ spl3_36 ),
    inference(resolution,[],[f256,f191])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2))
        | r1_tarski(X0,X2) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f190])).

fof(f256,plain,
    ( ! [X21,X22] : r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X21,X22))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( spl3_36
    | ~ spl3_3
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f234,f224,f44,f255])).

fof(f224,plain,
    ( spl3_32
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k4_xboole_0(sK0,sK1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f234,plain,
    ( ! [X21,X22] : r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X21,X22))
    | ~ spl3_3
    | ~ spl3_32 ),
    inference(resolution,[],[f225,f45])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k4_xboole_0(sK0,sK1),X1) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f224])).

fof(f226,plain,
    ( spl3_32
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f212,f209,f71,f224])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f209,plain,
    ( spl3_31
  <=> ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X3)
        | r1_tarski(k4_xboole_0(X0,X1),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k4_xboole_0(sK0,sK1),X1) )
    | ~ spl3_9
    | ~ spl3_31 ),
    inference(resolution,[],[f210,f72])).

fof(f72,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f210,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X3)
        | r1_tarski(k4_xboole_0(X0,X1),X3) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,
    ( spl3_31
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f140,f135,f56,f209])).

fof(f56,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f135,plain,
    ( spl3_20
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f140,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_tarski(X2,X3)
        | r1_tarski(k4_xboole_0(X0,X1),X3) )
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(resolution,[],[f136,f57])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(X1,X2)
        | r1_tarski(X0,X2) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f136,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f135])).

fof(f192,plain,
    ( spl3_28
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f141,f135,f60,f190])).

fof(f60,plain,
    ( spl3_7
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,X2)
        | ~ r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2)) )
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(superposition,[],[f136,f61])).

fof(f61,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f156,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f31,f154])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f137,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f29,f135])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f133,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f28,f131])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f94,plain,
    ( spl3_13
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f90,f60,f52,f92])).

fof(f52,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,
    ( ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( X0 != X0
        | r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) )
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(superposition,[],[f53,f61])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f73,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f69,f66,f44,f71])).

fof(f66,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f69,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f67,f45])).

fof(f67,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f63,f56,f34,f66])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f62,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f60])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f58,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f54,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f42,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f21,f34])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (13231)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  % (13231)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f512,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f37,f42,f46,f54,f58,f62,f68,f73,f94,f133,f137,f156,f192,f211,f226,f257,f265,f349,f477,f505,f511])).
% 0.21/0.43  fof(f511,plain,(
% 0.21/0.43    spl3_2 | ~spl3_19 | ~spl3_66),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f510])).
% 0.21/0.43  fof(f510,plain,(
% 0.21/0.43    $false | (spl3_2 | ~spl3_19 | ~spl3_66)),
% 0.21/0.43    inference(subsumption_resolution,[],[f41,f506])).
% 0.21/0.43  fof(f506,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,sK1))) ) | (~spl3_19 | ~spl3_66)),
% 0.21/0.43    inference(resolution,[],[f504,f132])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) ) | ~spl3_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f131])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    spl3_19 <=> ! [X1,X0,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.43  fof(f504,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK0,sK1))) ) | ~spl3_66),
% 0.21/0.43    inference(avatar_component_clause,[],[f503])).
% 0.21/0.43  fof(f503,plain,(
% 0.21/0.43    spl3_66 <=> ! [X0] : r1_xboole_0(X0,k4_xboole_0(sK0,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) | spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f505,plain,(
% 0.21/0.43    spl3_66 | ~spl3_3 | ~spl3_64),
% 0.21/0.43    inference(avatar_split_clause,[],[f485,f475,f44,f503])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl3_3 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f475,plain,(
% 0.21/0.43    spl3_64 <=> ! [X1,X0] : (r1_xboole_0(X0,k4_xboole_0(sK0,sK1)) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.43  fof(f485,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK0,sK1))) ) | (~spl3_3 | ~spl3_64)),
% 0.21/0.43    inference(resolution,[],[f476,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f476,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(sK0,sK1))) ) | ~spl3_64),
% 0.21/0.43    inference(avatar_component_clause,[],[f475])).
% 0.21/0.43  fof(f477,plain,(
% 0.21/0.43    spl3_64 | ~spl3_37 | ~spl3_48),
% 0.21/0.43    inference(avatar_split_clause,[],[f468,f347,f263,f475])).
% 0.21/0.43  fof(f263,plain,(
% 0.21/0.43    spl3_37 <=> ! [X0] : r1_tarski(k4_xboole_0(sK0,sK1),X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.43  fof(f347,plain,(
% 0.21/0.43    spl3_48 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(X0,X1) | ~r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(X2,X3))) | ~r1_tarski(X0,X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.43  fof(f468,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(sK0,sK1)) | ~r1_tarski(X0,X1)) ) | (~spl3_37 | ~spl3_48)),
% 0.21/0.43    inference(resolution,[],[f348,f264])).
% 0.21/0.43  fof(f264,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,sK1),X0)) ) | ~spl3_37),
% 0.21/0.43    inference(avatar_component_clause,[],[f263])).
% 0.21/0.43  fof(f348,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(X2,X3))) | r1_xboole_0(X0,X1) | ~r1_tarski(X0,X2)) ) | ~spl3_48),
% 0.21/0.43    inference(avatar_component_clause,[],[f347])).
% 0.21/0.43  fof(f349,plain,(
% 0.21/0.43    spl3_48 | ~spl3_13 | ~spl3_23),
% 0.21/0.43    inference(avatar_split_clause,[],[f184,f154,f92,f347])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    spl3_13 <=> ! [X1,X0] : r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.43  fof(f154,plain,(
% 0.21/0.43    spl3_23 <=> ! [X1,X3,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.43  fof(f184,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X1) | ~r1_tarski(X1,k4_xboole_0(X2,k2_xboole_0(X2,X3))) | ~r1_tarski(X0,X2)) ) | (~spl3_13 | ~spl3_23)),
% 0.21/0.43    inference(resolution,[],[f155,f93])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) ) | ~spl3_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f92])).
% 0.21/0.43  fof(f155,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X1,X3) | r1_xboole_0(X0,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) ) | ~spl3_23),
% 0.21/0.43    inference(avatar_component_clause,[],[f154])).
% 0.21/0.43  fof(f265,plain,(
% 0.21/0.43    spl3_37 | ~spl3_28 | ~spl3_36),
% 0.21/0.43    inference(avatar_split_clause,[],[f258,f255,f190,f263])).
% 0.21/0.43  fof(f190,plain,(
% 0.21/0.43    spl3_28 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.43  fof(f255,plain,(
% 0.21/0.43    spl3_36 <=> ! [X22,X21] : r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X21,X22))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.43  fof(f258,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,sK1),X0)) ) | (~spl3_28 | ~spl3_36)),
% 0.21/0.43    inference(resolution,[],[f256,f191])).
% 0.21/0.43  fof(f191,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2)) | r1_tarski(X0,X2)) ) | ~spl3_28),
% 0.21/0.43    inference(avatar_component_clause,[],[f190])).
% 0.21/0.43  fof(f256,plain,(
% 0.21/0.43    ( ! [X21,X22] : (r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X21,X22))) ) | ~spl3_36),
% 0.21/0.43    inference(avatar_component_clause,[],[f255])).
% 0.21/0.43  fof(f257,plain,(
% 0.21/0.43    spl3_36 | ~spl3_3 | ~spl3_32),
% 0.21/0.43    inference(avatar_split_clause,[],[f234,f224,f44,f255])).
% 0.21/0.43  fof(f224,plain,(
% 0.21/0.43    spl3_32 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(sK0,sK1),X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.43  fof(f234,plain,(
% 0.21/0.43    ( ! [X21,X22] : (r1_tarski(k4_xboole_0(sK0,sK1),k2_xboole_0(X21,X22))) ) | (~spl3_3 | ~spl3_32)),
% 0.21/0.43    inference(resolution,[],[f225,f45])).
% 0.21/0.43  fof(f225,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(sK0,sK1),X1)) ) | ~spl3_32),
% 0.21/0.43    inference(avatar_component_clause,[],[f224])).
% 0.21/0.43  fof(f226,plain,(
% 0.21/0.43    spl3_32 | ~spl3_9 | ~spl3_31),
% 0.21/0.43    inference(avatar_split_clause,[],[f212,f209,f71,f224])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl3_9 <=> ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.43  fof(f209,plain,(
% 0.21/0.43    spl3_31 <=> ! [X1,X3,X0,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | r1_tarski(k4_xboole_0(X0,X1),X3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.43  fof(f212,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(sK0,sK1),X1)) ) | (~spl3_9 | ~spl3_31)),
% 0.21/0.43    inference(resolution,[],[f210,f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f71])).
% 0.21/0.43  fof(f210,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | r1_tarski(k4_xboole_0(X0,X1),X3)) ) | ~spl3_31),
% 0.21/0.43    inference(avatar_component_clause,[],[f209])).
% 0.21/0.43  fof(f211,plain,(
% 0.21/0.43    spl3_31 | ~spl3_6 | ~spl3_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f140,f135,f56,f209])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    spl3_6 <=> ! [X1,X0,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    spl3_20 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.43  fof(f140,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | r1_tarski(k4_xboole_0(X0,X1),X3)) ) | (~spl3_6 | ~spl3_20)),
% 0.21/0.43    inference(resolution,[],[f136,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f56])).
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_20),
% 0.21/0.43    inference(avatar_component_clause,[],[f135])).
% 0.21/0.43  fof(f192,plain,(
% 0.21/0.43    spl3_28 | ~spl3_7 | ~spl3_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f141,f135,f60,f190])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl3_7 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f141,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X0,X1)),X2))) ) | (~spl3_7 | ~spl3_20)),
% 0.21/0.43    inference(superposition,[],[f136,f61])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) ) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f156,plain,(
% 0.21/0.43    spl3_23),
% 0.21/0.43    inference(avatar_split_clause,[],[f31,f154])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.21/0.43  fof(f137,plain,(
% 0.21/0.43    spl3_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f135])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    spl3_19),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f131])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    spl3_13 | ~spl3_5 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f90,f60,f52,f92])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    spl3_5 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) ) | (~spl3_5 | ~spl3_7)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f89])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    ( ! [X0,X1] : (X0 != X0 | r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) ) | (~spl3_5 | ~spl3_7)),
% 0.21/0.43    inference(superposition,[],[f53,f61])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f52])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl3_9 | ~spl3_3 | ~spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f69,f66,f44,f71])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    spl3_8 <=> ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK0,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) ) | (~spl3_3 | ~spl3_8)),
% 0.21/0.43    inference(resolution,[],[f67,f45])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK0,X0)) ) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f66])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl3_8 | ~spl3_1 | ~spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f63,f56,f34,f66])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK0,X0)) ) | (~spl3_1 | ~spl3_6)),
% 0.21/0.43    inference(resolution,[],[f57,f36])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f34])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f60])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.21/0.43    inference(definition_unfolding,[],[f24,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f56])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f52])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f44])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ~spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f39])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.43    inference(negated_conjecture,[],[f9])).
% 0.21/0.43  fof(f9,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f34])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f19])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (13231)------------------------------
% 0.21/0.43  % (13231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (13231)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (13231)Memory used [KB]: 6524
% 0.21/0.43  % (13231)Time elapsed: 0.017 s
% 0.21/0.43  % (13231)------------------------------
% 0.21/0.43  % (13231)------------------------------
% 0.21/0.43  % (13223)Success in time 0.074 s
%------------------------------------------------------------------------------
