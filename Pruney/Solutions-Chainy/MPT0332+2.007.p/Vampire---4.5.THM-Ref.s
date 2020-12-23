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
% DateTime   : Thu Dec  3 12:43:09 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  127 (2184 expanded)
%              Number of leaves         :   27 ( 699 expanded)
%              Depth                    :   24
%              Number of atoms          :  227 (2455 expanded)
%              Number of equality atoms :  110 (2177 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f1135,f1463,f1519,f1946,f2141,f2185,f2186,f2187])).

fof(f2187,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | sK2 != k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | sK2 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK1),sK2)),k2_tarski(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2186,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2))
    | r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2185,plain,
    ( spl3_32
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f2157,f1960,f2182])).

fof(f2182,plain,
    ( spl3_32
  <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f1960,plain,
    ( spl3_30
  <=> k2_tarski(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f2157,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_30 ),
    inference(superposition,[],[f146,f1962])).

fof(f1962,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f1960])).

fof(f146,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f51,f52])).

fof(f52,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2141,plain,
    ( spl3_30
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f1830,f1516,f1960])).

fof(f1516,plain,
    ( spl3_24
  <=> k1_xboole_0 = k4_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1830,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1800,f713])).

fof(f713,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(global_subsumption,[],[f526,f676])).

fof(f676,plain,(
    ! [X3] : r1_tarski(k4_xboole_0(X3,k1_xboole_0),X3) ),
    inference(trivial_inequality_removal,[],[f662])).

fof(f662,plain,(
    ! [X3] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(X3,k1_xboole_0),X3) ) ),
    inference(superposition,[],[f37,f597])).

fof(f597,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k1_xboole_0),X3) ),
    inference(superposition,[],[f579,f170])).

fof(f170,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f160,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f160,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1) ),
    inference(superposition,[],[f141,f52])).

fof(f141,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f99,f114])).

fof(f114,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f113,f43])).

fof(f113,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f54,f52])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f99,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f33,f43])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f579,plain,(
    ! [X8,X9] : k4_xboole_0(X9,X8) = k4_xboole_0(X9,k4_xboole_0(X8,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f149,f312])).

fof(f312,plain,(
    ! [X14,X13] : k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14) = k4_xboole_0(X13,X14) ),
    inference(forward_demodulation,[],[f311,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f311,plain,(
    ! [X14,X13] : k4_xboole_0(k5_xboole_0(X13,k1_xboole_0),X14) = k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14) ),
    inference(forward_demodulation,[],[f310,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f310,plain,(
    ! [X14,X13] : k4_xboole_0(k5_xboole_0(X13,k1_xboole_0),X14) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14))) ),
    inference(forward_demodulation,[],[f282,f171])).

fof(f171,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f161,f43])).

fof(f161,plain,(
    ! [X2] : k5_xboole_0(X2,X2) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f141,f53])).

fof(f282,plain,(
    ! [X14,X13] : k4_xboole_0(k5_xboole_0(X13,k1_xboole_0),X14) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14),k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14))) ),
    inference(superposition,[],[f197,f171])).

fof(f197,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(forward_demodulation,[],[f196,f51])).

fof(f196,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(forward_demodulation,[],[f50,f51])).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) ),
    inference(definition_unfolding,[],[f31,f34,f34,f34])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f149,plain,(
    ! [X8,X9] : k4_xboole_0(k4_xboole_0(X9,k1_xboole_0),X8) = k4_xboole_0(X9,k4_xboole_0(X8,k1_xboole_0)) ),
    inference(superposition,[],[f51,f114])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f526,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k1_xboole_0) = X0
      | ~ r1_tarski(k4_xboole_0(X0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f506,f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f506,plain,(
    ! [X0] : r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(trivial_inequality_removal,[],[f496])).

fof(f496,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0)) ) ),
    inference(superposition,[],[f37,f457])).

fof(f457,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f312,f170])).

fof(f1800,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)
    | ~ spl3_24 ),
    inference(superposition,[],[f713,f1539])).

fof(f1539,plain,
    ( ! [X4] : k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4) = k4_xboole_0(k2_tarski(sK0,sK1),X4)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1538,f141])).

fof(f1538,plain,
    ( ! [X4] : k4_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))),X4) = k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4)
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1537,f114])).

fof(f1537,plain,
    ( ! [X4] : k4_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))),X4) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4))
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1536,f713])).

fof(f1536,plain,
    ( ! [X4] : k4_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))),X4) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4),k1_xboole_0))
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1527,f171])).

fof(f1527,plain,
    ( ! [X4] : k4_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))),X4) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4),k4_xboole_0(k1_xboole_0,X4)))
    | ~ spl3_24 ),
    inference(superposition,[],[f197,f1518])).

fof(f1518,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f1516])).

fof(f1946,plain,
    ( spl3_29
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f1829,f1516,f1943])).

fof(f1943,plain,
    ( spl3_29
  <=> r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f1829,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2))
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f1799,f713])).

fof(f1799,plain,
    ( r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0),k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2))
    | ~ spl3_24 ),
    inference(superposition,[],[f676,f1539])).

fof(f1519,plain,
    ( spl3_24
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f1511,f83,f1516])).

fof(f83,plain,
    ( spl3_5
  <=> sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1511,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1481,f170])).

fof(f1481,plain,
    ( k4_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) = k4_xboole_0(sK2,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f1147,f84])).

fof(f84,plain,
    ( sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f1147,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,k2_tarski(sK0,sK1)),sK2) = k4_xboole_0(X0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f1140,f249])).

fof(f249,plain,(
    ! [X6,X5] : k5_xboole_0(X5,X6) = k5_xboole_0(X6,X5) ),
    inference(superposition,[],[f141,f230])).

fof(f230,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f215,f42])).

fof(f215,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f141,f104])).

fof(f104,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f33,f43])).

fof(f1140,plain,
    ( ! [X0] : k4_xboole_0(k4_xboole_0(X0,k2_tarski(sK0,sK1)),sK2) = k4_xboole_0(X0,k5_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl3_5 ),
    inference(superposition,[],[f51,f84])).

fof(f1463,plain,
    ( ~ spl3_23
    | ~ spl3_5
    | spl3_22 ),
    inference(avatar_split_clause,[],[f1443,f1359,f83,f1460])).

fof(f1460,plain,
    ( spl3_23
  <=> r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1359,plain,
    ( spl3_22
  <=> sK2 = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1443,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | ~ spl3_5
    | spl3_22 ),
    inference(trivial_inequality_removal,[],[f1442])).

fof(f1442,plain,
    ( sK2 != sK2
    | ~ r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | ~ spl3_5
    | spl3_22 ),
    inference(forward_demodulation,[],[f1441,f84])).

fof(f1441,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | spl3_22 ),
    inference(forward_demodulation,[],[f1395,f146])).

fof(f1395,plain,
    ( sK2 != k4_xboole_0(k4_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | spl3_22 ),
    inference(superposition,[],[f1361,f314])).

fof(f314,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(k5_xboole_0(X3,X2),X4) = k4_xboole_0(k4_xboole_0(X3,X2),X4)
      | ~ r1_tarski(k4_xboole_0(X2,X3),X4) ) ),
    inference(forward_demodulation,[],[f284,f53])).

fof(f284,plain,(
    ! [X4,X2,X3] :
      ( k4_xboole_0(k5_xboole_0(X3,X2),X4) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X3,X2),X4),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X3,X2),X4)))
      | ~ r1_tarski(k4_xboole_0(X2,X3),X4) ) ),
    inference(superposition,[],[f197,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1361,plain,
    ( sK2 != k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f1359])).

fof(f1135,plain,
    ( spl3_1
    | spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f1128])).

fof(f1128,plain,
    ( $false
    | spl3_1
    | spl3_2
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f60,f65,f85,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f85,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f65,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f60,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f71,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f49,f68])).

fof(f68,plain,
    ( spl3_3
  <=> sK2 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK1),sK2)),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f49,plain,(
    sK2 != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK1),sK2)),k2_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f30,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f66,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f28,f58])).

fof(f28,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:03:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (13146)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (13139)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (13143)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (13141)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (13142)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (13161)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (13153)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (13144)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (13156)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (13140)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (13145)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (13157)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (13164)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (13166)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (13168)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (13168)Refutation not found, incomplete strategy% (13168)------------------------------
% 0.21/0.55  % (13168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (13168)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (13168)Memory used [KB]: 1663
% 0.21/0.55  % (13168)Time elapsed: 0.001 s
% 0.21/0.55  % (13168)------------------------------
% 0.21/0.55  % (13168)------------------------------
% 0.21/0.55  % (13149)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (13148)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (13165)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (13149)Refutation not found, incomplete strategy% (13149)------------------------------
% 0.21/0.56  % (13149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13155)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (13150)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (13158)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (13159)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.47/0.56  % (13154)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.47/0.56  % (13151)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.47/0.56  % (13152)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.47/0.56  % (13163)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.56  % (13160)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.47/0.56  % (13155)Refutation not found, incomplete strategy% (13155)------------------------------
% 1.47/0.56  % (13155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (13155)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (13155)Memory used [KB]: 10618
% 1.47/0.56  % (13155)Time elapsed: 0.142 s
% 1.47/0.56  % (13155)------------------------------
% 1.47/0.56  % (13155)------------------------------
% 1.47/0.56  % (13156)Refutation not found, incomplete strategy% (13156)------------------------------
% 1.47/0.56  % (13156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (13162)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.47/0.56  % (13156)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (13156)Memory used [KB]: 1791
% 1.47/0.56  % (13156)Time elapsed: 0.144 s
% 1.47/0.56  % (13156)------------------------------
% 1.47/0.56  % (13156)------------------------------
% 1.47/0.56  % (13147)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.47/0.57  % (13167)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.47/0.57  % (13167)Refutation not found, incomplete strategy% (13167)------------------------------
% 1.47/0.57  % (13167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (13167)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (13167)Memory used [KB]: 10746
% 1.47/0.57  % (13167)Time elapsed: 0.133 s
% 1.47/0.57  % (13167)------------------------------
% 1.47/0.57  % (13167)------------------------------
% 1.47/0.58  % (13149)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (13149)Memory used [KB]: 10746
% 1.47/0.58  % (13149)Time elapsed: 0.145 s
% 1.47/0.58  % (13149)------------------------------
% 1.47/0.58  % (13149)------------------------------
% 2.11/0.69  % (13239)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.11/0.69  % (13228)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.11/0.70  % (13225)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.11/0.70  % (13162)Refutation found. Thanks to Tanya!
% 2.11/0.70  % SZS status Theorem for theBenchmark
% 2.11/0.70  % SZS output start Proof for theBenchmark
% 2.11/0.70  fof(f2188,plain,(
% 2.11/0.70    $false),
% 2.11/0.70    inference(avatar_sat_refutation,[],[f61,f66,f71,f1135,f1463,f1519,f1946,f2141,f2185,f2186,f2187])).
% 2.11/0.70  fof(f2187,plain,(
% 2.11/0.70    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | sK2 != k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | sK2 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK1),sK2)),k2_tarski(sK0,sK1))),
% 2.11/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.11/0.70  fof(f2186,plain,(
% 2.11/0.70    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2) | ~r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)) | r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))),
% 2.11/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.11/0.70  fof(f2185,plain,(
% 2.11/0.70    spl3_32 | ~spl3_30),
% 2.11/0.70    inference(avatar_split_clause,[],[f2157,f1960,f2182])).
% 2.11/0.70  fof(f2182,plain,(
% 2.11/0.70    spl3_32 <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.11/0.70  fof(f1960,plain,(
% 2.11/0.70    spl3_30 <=> k2_tarski(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.11/0.70  fof(f2157,plain,(
% 2.11/0.70    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_30),
% 2.11/0.70    inference(superposition,[],[f146,f1962])).
% 2.11/0.70  fof(f1962,plain,(
% 2.11/0.70    k2_tarski(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2) | ~spl3_30),
% 2.11/0.70    inference(avatar_component_clause,[],[f1960])).
% 2.11/0.70  fof(f146,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 2.11/0.70    inference(superposition,[],[f51,f52])).
% 2.11/0.70  fof(f52,plain,(
% 2.11/0.70    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.11/0.70    inference(definition_unfolding,[],[f35,f34])).
% 2.11/0.70  fof(f34,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f11])).
% 2.11/0.70  fof(f11,axiom,(
% 2.11/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.11/0.70  fof(f35,plain,(
% 2.11/0.70    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.11/0.70    inference(cnf_transformation,[],[f19])).
% 2.11/0.70  fof(f19,plain,(
% 2.11/0.70    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.11/0.70    inference(rectify,[],[f1])).
% 2.11/0.70  fof(f1,axiom,(
% 2.11/0.70    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.11/0.70  fof(f51,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 2.11/0.70    inference(definition_unfolding,[],[f32,f34])).
% 2.11/0.70  fof(f32,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f6])).
% 2.11/0.70  fof(f6,axiom,(
% 2.11/0.70    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.11/0.70  fof(f2141,plain,(
% 2.11/0.70    spl3_30 | ~spl3_24),
% 2.11/0.70    inference(avatar_split_clause,[],[f1830,f1516,f1960])).
% 2.11/0.70  fof(f1516,plain,(
% 2.11/0.70    spl3_24 <=> k1_xboole_0 = k4_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.11/0.70  fof(f1830,plain,(
% 2.11/0.70    k2_tarski(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2) | ~spl3_24),
% 2.11/0.70    inference(forward_demodulation,[],[f1800,f713])).
% 2.11/0.70  fof(f713,plain,(
% 2.11/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.11/0.70    inference(global_subsumption,[],[f526,f676])).
% 2.11/0.70  fof(f676,plain,(
% 2.11/0.70    ( ! [X3] : (r1_tarski(k4_xboole_0(X3,k1_xboole_0),X3)) )),
% 2.11/0.70    inference(trivial_inequality_removal,[],[f662])).
% 2.11/0.70  fof(f662,plain,(
% 2.11/0.70    ( ! [X3] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(X3,k1_xboole_0),X3)) )),
% 2.11/0.70    inference(superposition,[],[f37,f597])).
% 2.11/0.70  fof(f597,plain,(
% 2.11/0.70    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,k1_xboole_0),X3)) )),
% 2.11/0.70    inference(superposition,[],[f579,f170])).
% 2.11/0.70  fof(f170,plain,(
% 2.11/0.70    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 2.11/0.70    inference(forward_demodulation,[],[f160,f43])).
% 2.11/0.70  fof(f43,plain,(
% 2.11/0.70    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f9])).
% 2.11/0.70  fof(f9,axiom,(
% 2.11/0.70    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.11/0.70  fof(f160,plain,(
% 2.11/0.70    ( ! [X1] : (k4_xboole_0(X1,X1) = k5_xboole_0(X1,X1)) )),
% 2.11/0.70    inference(superposition,[],[f141,f52])).
% 2.11/0.70  fof(f141,plain,(
% 2.11/0.70    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 2.11/0.70    inference(forward_demodulation,[],[f99,f114])).
% 2.11/0.70  fof(f114,plain,(
% 2.11/0.70    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.11/0.70    inference(forward_demodulation,[],[f113,f43])).
% 2.11/0.70  fof(f113,plain,(
% 2.11/0.70    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 2.11/0.70    inference(forward_demodulation,[],[f54,f52])).
% 2.11/0.70  fof(f54,plain,(
% 2.11/0.70    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0) )),
% 2.11/0.70    inference(definition_unfolding,[],[f47,f48])).
% 2.11/0.70  fof(f48,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 2.11/0.70    inference(definition_unfolding,[],[f41,f34])).
% 2.11/0.70  fof(f41,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f10])).
% 2.11/0.70  fof(f10,axiom,(
% 2.11/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.11/0.70  fof(f47,plain,(
% 2.11/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.11/0.70    inference(cnf_transformation,[],[f20])).
% 2.11/0.70  fof(f20,plain,(
% 2.11/0.70    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.11/0.70    inference(rectify,[],[f2])).
% 2.11/0.70  fof(f2,axiom,(
% 2.11/0.70    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.11/0.70  fof(f99,plain,(
% 2.11/0.70    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 2.11/0.70    inference(superposition,[],[f33,f43])).
% 2.11/0.70  fof(f33,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f8])).
% 2.11/0.70  fof(f8,axiom,(
% 2.11/0.70    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.11/0.70  fof(f579,plain,(
% 2.11/0.70    ( ! [X8,X9] : (k4_xboole_0(X9,X8) = k4_xboole_0(X9,k4_xboole_0(X8,k1_xboole_0))) )),
% 2.11/0.70    inference(forward_demodulation,[],[f149,f312])).
% 2.11/0.70  fof(f312,plain,(
% 2.11/0.70    ( ! [X14,X13] : (k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14) = k4_xboole_0(X13,X14)) )),
% 2.11/0.70    inference(forward_demodulation,[],[f311,f42])).
% 2.11/0.70  fof(f42,plain,(
% 2.11/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.11/0.70    inference(cnf_transformation,[],[f7])).
% 2.11/0.70  fof(f7,axiom,(
% 2.11/0.70    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.11/0.70  fof(f311,plain,(
% 2.11/0.70    ( ! [X14,X13] : (k4_xboole_0(k5_xboole_0(X13,k1_xboole_0),X14) = k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14)) )),
% 2.11/0.70    inference(forward_demodulation,[],[f310,f53])).
% 2.11/0.70  fof(f53,plain,(
% 2.11/0.70    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.11/0.70    inference(definition_unfolding,[],[f39,f34])).
% 2.11/0.70  fof(f39,plain,(
% 2.11/0.70    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.11/0.70    inference(cnf_transformation,[],[f5])).
% 2.11/0.70  fof(f5,axiom,(
% 2.11/0.70    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.11/0.70  fof(f310,plain,(
% 2.11/0.70    ( ! [X14,X13] : (k4_xboole_0(k5_xboole_0(X13,k1_xboole_0),X14) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14)))) )),
% 2.11/0.70    inference(forward_demodulation,[],[f282,f171])).
% 2.11/0.70  fof(f171,plain,(
% 2.11/0.70    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 2.11/0.70    inference(forward_demodulation,[],[f161,f43])).
% 2.11/0.70  fof(f161,plain,(
% 2.11/0.70    ( ! [X2] : (k5_xboole_0(X2,X2) = k4_xboole_0(k1_xboole_0,X2)) )),
% 2.11/0.70    inference(superposition,[],[f141,f53])).
% 2.11/0.70  fof(f282,plain,(
% 2.11/0.70    ( ! [X14,X13] : (k4_xboole_0(k5_xboole_0(X13,k1_xboole_0),X14) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14),k4_xboole_0(k4_xboole_0(k1_xboole_0,X14),k4_xboole_0(k4_xboole_0(X13,k1_xboole_0),X14)))) )),
% 2.11/0.70    inference(superposition,[],[f197,f171])).
% 2.11/0.70  fof(f197,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(k4_xboole_0(X1,X0),X2),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 2.11/0.70    inference(forward_demodulation,[],[f196,f51])).
% 2.11/0.70  fof(f196,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 2.11/0.70    inference(forward_demodulation,[],[f50,f51])).
% 2.11/0.70  fof(f50,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))) )),
% 2.11/0.70    inference(definition_unfolding,[],[f31,f34,f34,f34])).
% 2.11/0.70  fof(f31,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 2.11/0.70    inference(cnf_transformation,[],[f12])).
% 2.11/0.70  fof(f12,axiom,(
% 2.11/0.70    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).
% 2.11/0.70  fof(f149,plain,(
% 2.11/0.70    ( ! [X8,X9] : (k4_xboole_0(k4_xboole_0(X9,k1_xboole_0),X8) = k4_xboole_0(X9,k4_xboole_0(X8,k1_xboole_0))) )),
% 2.11/0.70    inference(superposition,[],[f51,f114])).
% 2.11/0.70  fof(f37,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f25])).
% 2.11/0.70  fof(f25,plain,(
% 2.11/0.70    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.11/0.70    inference(nnf_transformation,[],[f4])).
% 2.11/0.70  fof(f4,axiom,(
% 2.11/0.70    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.11/0.70  fof(f526,plain,(
% 2.11/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0 | ~r1_tarski(k4_xboole_0(X0,k1_xboole_0),X0)) )),
% 2.11/0.70    inference(resolution,[],[f506,f46])).
% 2.11/0.70  fof(f46,plain,(
% 2.11/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f27])).
% 2.11/0.70  fof(f27,plain,(
% 2.11/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.70    inference(flattening,[],[f26])).
% 2.11/0.70  fof(f26,plain,(
% 2.11/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.11/0.70    inference(nnf_transformation,[],[f3])).
% 2.11/0.70  fof(f3,axiom,(
% 2.11/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.11/0.70  fof(f506,plain,(
% 2.11/0.70    ( ! [X0] : (r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.11/0.70    inference(trivial_inequality_removal,[],[f496])).
% 2.11/0.70  fof(f496,plain,(
% 2.11/0.70    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.11/0.70    inference(superposition,[],[f37,f457])).
% 2.11/0.70  fof(f457,plain,(
% 2.11/0.70    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) )),
% 2.11/0.70    inference(superposition,[],[f312,f170])).
% 2.11/0.70  fof(f1800,plain,(
% 2.11/0.70    k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0) = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2) | ~spl3_24),
% 2.11/0.70    inference(superposition,[],[f713,f1539])).
% 2.11/0.70  fof(f1539,plain,(
% 2.11/0.70    ( ! [X4] : (k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4) = k4_xboole_0(k2_tarski(sK0,sK1),X4)) ) | ~spl3_24),
% 2.11/0.70    inference(forward_demodulation,[],[f1538,f141])).
% 2.11/0.70  fof(f1538,plain,(
% 2.11/0.70    ( ! [X4] : (k4_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))),X4) = k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4)) ) | ~spl3_24),
% 2.11/0.70    inference(forward_demodulation,[],[f1537,f114])).
% 2.11/0.70  fof(f1537,plain,(
% 2.11/0.70    ( ! [X4] : (k4_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))),X4) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4))) ) | ~spl3_24),
% 2.11/0.70    inference(forward_demodulation,[],[f1536,f713])).
% 2.11/0.70  fof(f1536,plain,(
% 2.11/0.70    ( ! [X4] : (k4_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))),X4) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4),k1_xboole_0))) ) | ~spl3_24),
% 2.11/0.70    inference(forward_demodulation,[],[f1527,f171])).
% 2.11/0.70  fof(f1527,plain,(
% 2.11/0.70    ( ! [X4] : (k4_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))),X4) = k5_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k4_xboole_0(k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2),X4),k4_xboole_0(k1_xboole_0,X4)))) ) | ~spl3_24),
% 2.11/0.70    inference(superposition,[],[f197,f1518])).
% 2.11/0.70  fof(f1518,plain,(
% 2.11/0.70    k1_xboole_0 = k4_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_24),
% 2.11/0.70    inference(avatar_component_clause,[],[f1516])).
% 2.11/0.70  fof(f1946,plain,(
% 2.11/0.70    spl3_29 | ~spl3_24),
% 2.11/0.70    inference(avatar_split_clause,[],[f1829,f1516,f1943])).
% 2.11/0.70  fof(f1943,plain,(
% 2.11/0.70    spl3_29 <=> r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2))),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.11/0.70  fof(f1829,plain,(
% 2.11/0.70    r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)) | ~spl3_24),
% 2.11/0.70    inference(forward_demodulation,[],[f1799,f713])).
% 2.11/0.70  fof(f1799,plain,(
% 2.11/0.70    r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),k1_xboole_0),k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),sK2)) | ~spl3_24),
% 2.11/0.70    inference(superposition,[],[f676,f1539])).
% 2.11/0.70  fof(f1519,plain,(
% 2.11/0.70    spl3_24 | ~spl3_5),
% 2.11/0.70    inference(avatar_split_clause,[],[f1511,f83,f1516])).
% 2.11/0.70  fof(f83,plain,(
% 2.11/0.70    spl3_5 <=> sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.11/0.70  fof(f1511,plain,(
% 2.11/0.70    k1_xboole_0 = k4_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_5),
% 2.11/0.70    inference(forward_demodulation,[],[f1481,f170])).
% 2.11/0.70  fof(f1481,plain,(
% 2.11/0.70    k4_xboole_0(sK2,k5_xboole_0(sK2,k2_tarski(sK0,sK1))) = k4_xboole_0(sK2,sK2) | ~spl3_5),
% 2.11/0.70    inference(superposition,[],[f1147,f84])).
% 2.11/0.70  fof(f84,plain,(
% 2.11/0.70    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl3_5),
% 2.11/0.70    inference(avatar_component_clause,[],[f83])).
% 2.11/0.70  fof(f1147,plain,(
% 2.11/0.70    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,k2_tarski(sK0,sK1)),sK2) = k4_xboole_0(X0,k5_xboole_0(sK2,k2_tarski(sK0,sK1)))) ) | ~spl3_5),
% 2.11/0.70    inference(forward_demodulation,[],[f1140,f249])).
% 2.11/0.70  fof(f249,plain,(
% 2.11/0.70    ( ! [X6,X5] : (k5_xboole_0(X5,X6) = k5_xboole_0(X6,X5)) )),
% 2.11/0.70    inference(superposition,[],[f141,f230])).
% 2.11/0.70  fof(f230,plain,(
% 2.11/0.70    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 2.11/0.70    inference(forward_demodulation,[],[f215,f42])).
% 2.11/0.70  fof(f215,plain,(
% 2.11/0.70    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 2.11/0.70    inference(superposition,[],[f141,f104])).
% 2.11/0.70  fof(f104,plain,(
% 2.11/0.70    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 2.11/0.70    inference(superposition,[],[f33,f43])).
% 2.11/0.70  fof(f1140,plain,(
% 2.11/0.70    ( ! [X0] : (k4_xboole_0(k4_xboole_0(X0,k2_tarski(sK0,sK1)),sK2) = k4_xboole_0(X0,k5_xboole_0(k2_tarski(sK0,sK1),sK2))) ) | ~spl3_5),
% 2.11/0.70    inference(superposition,[],[f51,f84])).
% 2.11/0.70  fof(f1463,plain,(
% 2.11/0.70    ~spl3_23 | ~spl3_5 | spl3_22),
% 2.11/0.70    inference(avatar_split_clause,[],[f1443,f1359,f83,f1460])).
% 2.11/0.70  fof(f1460,plain,(
% 2.11/0.70    spl3_23 <=> r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.11/0.70  fof(f1359,plain,(
% 2.11/0.70    spl3_22 <=> sK2 = k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.11/0.70  fof(f1443,plain,(
% 2.11/0.70    ~r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | (~spl3_5 | spl3_22)),
% 2.11/0.70    inference(trivial_inequality_removal,[],[f1442])).
% 2.11/0.70  fof(f1442,plain,(
% 2.11/0.70    sK2 != sK2 | ~r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | (~spl3_5 | spl3_22)),
% 2.11/0.70    inference(forward_demodulation,[],[f1441,f84])).
% 2.11/0.70  fof(f1441,plain,(
% 2.11/0.70    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | spl3_22),
% 2.11/0.70    inference(forward_demodulation,[],[f1395,f146])).
% 2.11/0.70  fof(f1395,plain,(
% 2.11/0.70    sK2 != k4_xboole_0(k4_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | ~r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | spl3_22),
% 2.11/0.70    inference(superposition,[],[f1361,f314])).
% 2.11/0.70  fof(f314,plain,(
% 2.11/0.70    ( ! [X4,X2,X3] : (k4_xboole_0(k5_xboole_0(X3,X2),X4) = k4_xboole_0(k4_xboole_0(X3,X2),X4) | ~r1_tarski(k4_xboole_0(X2,X3),X4)) )),
% 2.11/0.70    inference(forward_demodulation,[],[f284,f53])).
% 2.11/0.70  fof(f284,plain,(
% 2.11/0.70    ( ! [X4,X2,X3] : (k4_xboole_0(k5_xboole_0(X3,X2),X4) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X3,X2),X4),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X3,X2),X4))) | ~r1_tarski(k4_xboole_0(X2,X3),X4)) )),
% 2.11/0.70    inference(superposition,[],[f197,f38])).
% 2.11/0.70  fof(f38,plain,(
% 2.11/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f25])).
% 2.11/0.70  fof(f1361,plain,(
% 2.11/0.70    sK2 != k4_xboole_0(k5_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | spl3_22),
% 2.11/0.70    inference(avatar_component_clause,[],[f1359])).
% 2.11/0.70  fof(f1135,plain,(
% 2.11/0.70    spl3_1 | spl3_2 | spl3_5),
% 2.11/0.70    inference(avatar_contradiction_clause,[],[f1128])).
% 2.11/0.70  fof(f1128,plain,(
% 2.11/0.70    $false | (spl3_1 | spl3_2 | spl3_5)),
% 2.11/0.70    inference(unit_resulting_resolution,[],[f60,f65,f85,f36])).
% 2.11/0.70  fof(f36,plain,(
% 2.11/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 2.11/0.70    inference(cnf_transformation,[],[f22])).
% 2.11/0.70  fof(f22,plain,(
% 2.11/0.70    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 2.11/0.70    inference(ennf_transformation,[],[f16])).
% 2.11/0.70  fof(f16,axiom,(
% 2.11/0.70    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 2.11/0.70  fof(f85,plain,(
% 2.11/0.70    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) | spl3_5),
% 2.11/0.70    inference(avatar_component_clause,[],[f83])).
% 2.11/0.70  fof(f65,plain,(
% 2.11/0.70    ~r2_hidden(sK1,sK2) | spl3_2),
% 2.11/0.70    inference(avatar_component_clause,[],[f63])).
% 2.11/0.70  fof(f63,plain,(
% 2.11/0.70    spl3_2 <=> r2_hidden(sK1,sK2)),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.11/0.70  fof(f60,plain,(
% 2.11/0.70    ~r2_hidden(sK0,sK2) | spl3_1),
% 2.11/0.70    inference(avatar_component_clause,[],[f58])).
% 2.11/0.70  fof(f58,plain,(
% 2.11/0.70    spl3_1 <=> r2_hidden(sK0,sK2)),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.11/0.70  fof(f71,plain,(
% 2.11/0.70    ~spl3_3),
% 2.11/0.70    inference(avatar_split_clause,[],[f49,f68])).
% 2.11/0.70  fof(f68,plain,(
% 2.11/0.70    spl3_3 <=> sK2 = k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK1),sK2)),k2_tarski(sK0,sK1))),
% 2.11/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.11/0.70  fof(f49,plain,(
% 2.11/0.70    sK2 != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_tarski(sK0,sK1),sK2)),k2_tarski(sK0,sK1))),
% 2.11/0.70    inference(definition_unfolding,[],[f30,f34])).
% 2.11/0.70  fof(f30,plain,(
% 2.11/0.70    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 2.11/0.70    inference(cnf_transformation,[],[f24])).
% 2.11/0.70  fof(f24,plain,(
% 2.11/0.70    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 2.11/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23])).
% 2.11/0.70  fof(f23,plain,(
% 2.11/0.70    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 2.11/0.70    introduced(choice_axiom,[])).
% 2.11/0.70  fof(f21,plain,(
% 2.11/0.70    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.11/0.70    inference(ennf_transformation,[],[f18])).
% 2.11/0.70  fof(f18,negated_conjecture,(
% 2.11/0.70    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.11/0.70    inference(negated_conjecture,[],[f17])).
% 2.11/0.70  fof(f17,conjecture,(
% 2.11/0.70    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.11/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 2.11/0.70  fof(f66,plain,(
% 2.11/0.70    ~spl3_2),
% 2.11/0.70    inference(avatar_split_clause,[],[f29,f63])).
% 2.11/0.70  fof(f29,plain,(
% 2.11/0.70    ~r2_hidden(sK1,sK2)),
% 2.11/0.70    inference(cnf_transformation,[],[f24])).
% 2.11/0.70  fof(f61,plain,(
% 2.11/0.70    ~spl3_1),
% 2.11/0.70    inference(avatar_split_clause,[],[f28,f58])).
% 2.11/0.70  fof(f28,plain,(
% 2.11/0.70    ~r2_hidden(sK0,sK2)),
% 2.11/0.70    inference(cnf_transformation,[],[f24])).
% 2.11/0.70  % SZS output end Proof for theBenchmark
% 2.11/0.70  % (13162)------------------------------
% 2.11/0.70  % (13162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.70  % (13162)Termination reason: Refutation
% 2.11/0.70  
% 2.11/0.70  % (13162)Memory used [KB]: 12281
% 2.11/0.70  % (13162)Time elapsed: 0.292 s
% 2.11/0.70  % (13162)------------------------------
% 2.11/0.70  % (13162)------------------------------
% 2.49/0.71  % (13229)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.49/0.71  % (13233)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.49/0.72  % (13138)Success in time 0.351 s
%------------------------------------------------------------------------------
