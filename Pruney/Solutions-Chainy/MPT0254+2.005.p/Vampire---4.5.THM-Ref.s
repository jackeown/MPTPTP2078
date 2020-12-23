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
% DateTime   : Thu Dec  3 12:39:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 368 expanded)
%              Number of leaves         :   28 ( 126 expanded)
%              Depth                    :   16
%              Number of atoms          :  282 ( 619 expanded)
%              Number of equality atoms :  103 ( 318 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f407,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f100,f110,f114,f121,f136,f168,f376,f387,f406])).

fof(f406,plain,
    ( ~ spl3_7
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f405,f370,f133,f164])).

fof(f164,plain,
    ( spl3_7
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f133,plain,
    ( spl3_6
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f370,plain,
    ( spl3_8
  <=> sK0 = sK2(sK0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f405,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(condensation,[],[f404])).

fof(f404,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | ~ r2_hidden(sK0,k1_xboole_0) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | ~ r2_hidden(sK0,k1_xboole_0)
        | ~ r2_hidden(X4,k1_xboole_0) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f400,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f400,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK0,k1_xboole_0)
        | ~ r2_hidden(X4,k1_xboole_0)
        | ~ r2_hidden(X4,k5_xboole_0(k1_xboole_0,k1_xboole_0)) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f393])).

fof(f393,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK0,k1_xboole_0)
        | ~ r2_hidden(X4,k1_xboole_0)
        | ~ r2_hidden(X4,k5_xboole_0(k1_xboole_0,k1_xboole_0))
        | sK0 != sK0 )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f171,f372])).

fof(f372,plain,
    ( sK0 = sK2(sK0,sK0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f370])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(sK0,sK0,X0),X0)
        | ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k5_xboole_0(k1_xboole_0,X0))
        | sK0 != sK2(sK0,sK0,X0) )
    | ~ spl3_6 ),
    inference(superposition,[],[f147,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | sK2(X0,X1,X2) != X0 ) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) != X0
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k2_tarski(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f147,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
        | ~ r2_hidden(X2,k1_xboole_0) )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )
    | ~ spl3_6 ),
    inference(superposition,[],[f49,f135])).

fof(f135,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f387,plain,
    ( ~ spl3_6
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f78,f375,f156])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f146,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f146,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
        | r2_hidden(X3,k1_xboole_0) )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )
    | ~ spl3_6 ),
    inference(superposition,[],[f50,f135])).

fof(f375,plain,
    ( ! [X26] : ~ r2_hidden(X26,k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl3_9
  <=> ! [X26] : ~ r2_hidden(X26,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f78,plain,(
    ! [X0,X3] : r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f60])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f376,plain,
    ( spl3_8
    | spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f368,f133,f374,f370])).

fof(f368,plain,
    ( ! [X26] :
        ( ~ r2_hidden(X26,k1_xboole_0)
        | sK0 = sK2(sK0,sK0,k1_xboole_0) )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f367])).

fof(f367,plain,
    ( ! [X26] :
        ( ~ r2_hidden(X26,k1_xboole_0)
        | ~ r2_hidden(X26,k1_xboole_0)
        | sK0 = sK2(sK0,sK0,k1_xboole_0) )
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f364,f28])).

fof(f364,plain,
    ( ! [X26] :
        ( ~ r2_hidden(X26,k1_xboole_0)
        | sK0 = sK2(sK0,sK0,k1_xboole_0)
        | ~ r2_hidden(X26,k5_xboole_0(k1_xboole_0,k1_xboole_0)) )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,
    ( ! [X26] :
        ( ~ r2_hidden(X26,k1_xboole_0)
        | sK0 = sK2(sK0,sK0,k1_xboole_0)
        | ~ r2_hidden(X26,k5_xboole_0(k1_xboole_0,k1_xboole_0))
        | sK0 = sK2(sK0,sK0,k1_xboole_0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f174,f183])).

fof(f183,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | sK0 = X1 )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | sK0 = X1
        | sK0 = X1 )
    | ~ spl3_6 ),
    inference(resolution,[],[f175,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f60])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f175,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
        | ~ r2_hidden(X1,k1_xboole_0) )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,k1_xboole_0)
        | r2_hidden(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )
    | ~ spl3_6 ),
    inference(resolution,[],[f147,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f174,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK2(sK0,sK0,X4),X4)
        | ~ r2_hidden(X5,k1_xboole_0)
        | sK0 = sK2(sK0,sK0,X4)
        | ~ r2_hidden(X5,k5_xboole_0(k1_xboole_0,X4)) )
    | ~ spl3_6 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k5_xboole_0(k1_xboole_0,X4))
        | ~ r2_hidden(X5,k1_xboole_0)
        | sK0 = sK2(sK0,sK0,X4)
        | r2_hidden(sK2(sK0,sK0,X4),X4)
        | sK0 = sK2(sK0,sK0,X4) )
    | ~ spl3_6 ),
    inference(superposition,[],[f147,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
      | sK2(X0,X1,X2) = X1
      | r2_hidden(sK2(X0,X1,X2),X2)
      | sK2(X0,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X0
      | sK2(X0,X1,X2) = X1
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k2_tarski(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f168,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f158,f133,f164])).

fof(f158,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(resolution,[],[f156,f80])).

fof(f80,plain,(
    ! [X3,X1] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f136,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f131,f118,f133])).

fof(f118,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f131,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f128,f28])).

fof(f128,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0))
    | ~ spl3_5 ),
    inference(superposition,[],[f66,f120])).

fof(f120,plain,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))) ),
    inference(definition_unfolding,[],[f27,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f35,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f60])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f121,plain,
    ( spl3_5
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f116,f103,f84,f118])).

fof(f84,plain,
    ( spl3_1
  <=> k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f103,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f116,plain,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f86,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f86,plain,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f114,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f26,f109])).

fof(f109,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_4
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f110,plain,
    ( spl3_3
    | ~ spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f101,f97,f107,f103])).

fof(f97,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f101,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(resolution,[],[f99,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f99,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f100,plain,
    ( spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f94,f84,f97])).

fof(f94,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f67,f86])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f61])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f87,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f82,f84])).

fof(f82,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f65,f68])).

fof(f68,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f31,f60,f60])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f65,plain,(
    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f25,f61,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f60])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:14:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (4442)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (4442)Refutation not found, incomplete strategy% (4442)------------------------------
% 0.21/0.52  % (4442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4442)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4442)Memory used [KB]: 10618
% 0.21/0.52  % (4442)Time elapsed: 0.107 s
% 0.21/0.52  % (4452)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (4442)------------------------------
% 0.21/0.52  % (4442)------------------------------
% 0.21/0.52  % (4444)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (4458)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (4433)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (4450)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (4458)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f407,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f87,f100,f110,f114,f121,f136,f168,f376,f387,f406])).
% 0.21/0.56  fof(f406,plain,(
% 0.21/0.56    ~spl3_7 | ~spl3_6 | ~spl3_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f405,f370,f133,f164])).
% 0.21/0.56  fof(f164,plain,(
% 0.21/0.56    spl3_7 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    spl3_6 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.56  fof(f370,plain,(
% 0.21/0.56    spl3_8 <=> sK0 = sK2(sK0,sK0,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.56  fof(f405,plain,(
% 0.21/0.56    ~r2_hidden(sK0,k1_xboole_0) | (~spl3_6 | ~spl3_8)),
% 0.21/0.56    inference(condensation,[],[f404])).
% 0.21/0.56  fof(f404,plain,(
% 0.21/0.56    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(sK0,k1_xboole_0)) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f403])).
% 0.21/0.56  fof(f403,plain,(
% 0.21/0.56    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0)) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.56    inference(forward_demodulation,[],[f400,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.56  fof(f400,plain,(
% 0.21/0.56    ( ! [X4] : (~r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,k5_xboole_0(k1_xboole_0,k1_xboole_0))) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f393])).
% 0.21/0.56  fof(f393,plain,(
% 0.21/0.56    ( ! [X4] : (~r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(X4,k1_xboole_0) | ~r2_hidden(X4,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | sK0 != sK0) ) | (~spl3_6 | ~spl3_8)),
% 0.21/0.56    inference(superposition,[],[f171,f372])).
% 0.21/0.56  fof(f372,plain,(
% 0.21/0.56    sK0 = sK2(sK0,sK0,k1_xboole_0) | ~spl3_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f370])).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(sK2(sK0,sK0,X0),X0) | ~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k5_xboole_0(k1_xboole_0,X0)) | sK0 != sK2(sK0,sK0,X0)) ) | ~spl3_6),
% 0.21/0.56    inference(superposition,[],[f147,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X2) | sK2(X0,X1,X2) != X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f42,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f34,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f40,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f52,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f53,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f54,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) != X0 | ~r2_hidden(sK2(X0,X1,X2),X2) | k2_tarski(X0,X1) = X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.56  fof(f147,plain,(
% 0.21/0.56    ( ! [X2] : (~r2_hidden(X2,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r2_hidden(X2,k1_xboole_0)) ) | ~spl3_6),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f143])).
% 0.21/0.56  fof(f143,plain,(
% 0.21/0.56    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | ~spl3_6),
% 0.21/0.56    inference(superposition,[],[f49,f135])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl3_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f133])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.56  fof(f387,plain,(
% 0.21/0.56    ~spl3_6 | ~spl3_9),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f378])).
% 0.21/0.56  fof(f378,plain,(
% 0.21/0.56    $false | (~spl3_6 | ~spl3_9)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f78,f375,f156])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | r2_hidden(X0,k1_xboole_0)) ) | ~spl3_6),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f150])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ) | ~spl3_6),
% 0.21/0.56    inference(resolution,[],[f146,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | r2_hidden(X3,k1_xboole_0)) ) | ~spl3_6),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f144])).
% 0.21/0.56  fof(f144,plain,(
% 0.21/0.56    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ) | ~spl3_6),
% 0.21/0.56    inference(superposition,[],[f50,f135])).
% 0.21/0.56  fof(f375,plain,(
% 0.21/0.56    ( ! [X26] : (~r2_hidden(X26,k1_xboole_0)) ) | ~spl3_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f374])).
% 0.21/0.56  fof(f374,plain,(
% 0.21/0.56    spl3_9 <=> ! [X26] : ~r2_hidden(X26,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0,X3] : (r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3))) )),
% 0.21/0.56    inference(equality_resolution,[],[f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3) != X2) )),
% 0.21/0.56    inference(equality_resolution,[],[f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 0.21/0.56    inference(definition_unfolding,[],[f47,f60])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f376,plain,(
% 0.21/0.56    spl3_8 | spl3_9 | ~spl3_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f368,f133,f374,f370])).
% 0.21/0.56  fof(f368,plain,(
% 0.21/0.56    ( ! [X26] : (~r2_hidden(X26,k1_xboole_0) | sK0 = sK2(sK0,sK0,k1_xboole_0)) ) | ~spl3_6),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f367])).
% 0.21/0.56  fof(f367,plain,(
% 0.21/0.56    ( ! [X26] : (~r2_hidden(X26,k1_xboole_0) | ~r2_hidden(X26,k1_xboole_0) | sK0 = sK2(sK0,sK0,k1_xboole_0)) ) | ~spl3_6),
% 0.21/0.56    inference(forward_demodulation,[],[f364,f28])).
% 0.21/0.56  fof(f364,plain,(
% 0.21/0.56    ( ! [X26] : (~r2_hidden(X26,k1_xboole_0) | sK0 = sK2(sK0,sK0,k1_xboole_0) | ~r2_hidden(X26,k5_xboole_0(k1_xboole_0,k1_xboole_0))) ) | ~spl3_6),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f363])).
% 0.21/0.56  fof(f363,plain,(
% 0.21/0.56    ( ! [X26] : (~r2_hidden(X26,k1_xboole_0) | sK0 = sK2(sK0,sK0,k1_xboole_0) | ~r2_hidden(X26,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | sK0 = sK2(sK0,sK0,k1_xboole_0)) ) | ~spl3_6),
% 0.21/0.56    inference(resolution,[],[f174,f183])).
% 0.21/0.56  fof(f183,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | sK0 = X1) ) | ~spl3_6),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f178])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | sK0 = X1 | sK0 = X1) ) | ~spl3_6),
% 0.21/0.56    inference(resolution,[],[f175,f81])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.21/0.56    inference(equality_resolution,[],[f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 0.21/0.56    inference(definition_unfolding,[],[f45,f60])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f175,plain,(
% 0.21/0.56    ( ! [X1] : (r2_hidden(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X1,k1_xboole_0)) ) | ~spl3_6),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f170])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ) | ~spl3_6),
% 0.21/0.56    inference(resolution,[],[f147,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    ( ! [X4,X5] : (r2_hidden(sK2(sK0,sK0,X4),X4) | ~r2_hidden(X5,k1_xboole_0) | sK0 = sK2(sK0,sK0,X4) | ~r2_hidden(X5,k5_xboole_0(k1_xboole_0,X4))) ) | ~spl3_6),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f173])).
% 0.21/0.56  fof(f173,plain,(
% 0.21/0.56    ( ! [X4,X5] : (~r2_hidden(X5,k5_xboole_0(k1_xboole_0,X4)) | ~r2_hidden(X5,k1_xboole_0) | sK0 = sK2(sK0,sK0,X4) | r2_hidden(sK2(sK0,sK0,X4),X4) | sK0 = sK2(sK0,sK0,X4)) ) | ~spl3_6),
% 0.21/0.56    inference(superposition,[],[f147,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2 | sK2(X0,X1,X2) = X1 | r2_hidden(sK2(X0,X1,X2),X2) | sK2(X0,X1,X2) = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f44,f60])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X0 | sK2(X0,X1,X2) = X1 | r2_hidden(sK2(X0,X1,X2),X2) | k2_tarski(X0,X1) = X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    spl3_7 | ~spl3_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f158,f133,f164])).
% 0.21/0.56  fof(f158,plain,(
% 0.21/0.56    r2_hidden(sK0,k1_xboole_0) | ~spl3_6),
% 0.21/0.56    inference(resolution,[],[f156,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X3,X1] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X1) != X2) )),
% 0.21/0.56    inference(equality_resolution,[],[f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 0.21/0.56    inference(definition_unfolding,[],[f46,f60])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    spl3_6 | ~spl3_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f131,f118,f133])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    spl3_5 <=> k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl3_5),
% 0.21/0.56    inference(forward_demodulation,[],[f128,f28])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)) | ~spl3_5),
% 0.21/0.56    inference(superposition,[],[f66,f120])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl3_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f118])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f27,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f35,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f36,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f33,f60])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    spl3_5 | ~spl3_1 | ~spl3_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f116,f103,f84,f118])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    spl3_1 <=> k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    spl3_3 <=> k1_xboole_0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (~spl3_1 | ~spl3_3)),
% 0.21/0.56    inference(backward_demodulation,[],[f86,f105])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    k1_xboole_0 = sK1 | ~spl3_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f103])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl3_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f84])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    spl3_4),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f111])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    $false | spl3_4),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f26,f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK1) | spl3_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f107])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    spl3_4 <=> r1_tarski(k1_xboole_0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    spl3_3 | ~spl3_4 | ~spl3_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f101,f97,f107,f103])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    spl3_2 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK1) | k1_xboole_0 = sK1 | ~spl3_2),
% 0.21/0.56    inference(resolution,[],[f99,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    r1_tarski(sK1,k1_xboole_0) | ~spl3_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f97])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    spl3_2 | ~spl3_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f94,f84,f97])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    r1_tarski(sK1,k1_xboole_0) | ~spl3_1),
% 0.21/0.56    inference(superposition,[],[f67,f86])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f30,f61])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    spl3_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f82,f84])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    k1_xboole_0 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 0.21/0.56    inference(forward_demodulation,[],[f65,f68])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f31,f60,f60])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    k1_xboole_0 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.21/0.56    inference(definition_unfolding,[],[f25,f61,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f29,f60])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.56    inference(ennf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.56    inference(negated_conjecture,[],[f21])).
% 0.21/0.56  fof(f21,conjecture,(
% 0.21/0.56    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (4458)------------------------------
% 0.21/0.56  % (4458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4458)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (4458)Memory used [KB]: 11001
% 0.21/0.56  % (4458)Time elapsed: 0.144 s
% 0.21/0.56  % (4458)------------------------------
% 0.21/0.56  % (4458)------------------------------
% 0.21/0.56  % (4428)Success in time 0.203 s
%------------------------------------------------------------------------------
