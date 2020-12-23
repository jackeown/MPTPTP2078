%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:12 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 258 expanded)
%              Number of leaves         :   38 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  321 ( 572 expanded)
%              Number of equality atoms :  113 ( 260 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1056,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f102,f122,f177,f213,f251,f275,f289,f301,f307,f312,f394,f435,f468,f1052,f1053,f1055])).

fof(f1055,plain,
    ( k1_tarski(sK0) != k5_xboole_0(sK1,sK2)
    | k5_xboole_0(sK1,sK2) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))
    | k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)))
    | k3_xboole_0(sK1,sK2) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))
    | sK2 != k3_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1053,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1052,plain,
    ( ~ spl3_6
    | spl3_7
    | ~ spl3_10
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f1051])).

fof(f1051,plain,
    ( $false
    | ~ spl3_6
    | spl3_7
    | ~ spl3_10
    | spl3_18 ),
    inference(subsumption_resolution,[],[f1045,f270])).

fof(f270,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl3_18
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f1045,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_6
    | spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f746,f116])).

fof(f116,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f746,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(resolution,[],[f445,f147])).

fof(f147,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | r1_xboole_0(sK1,X0) )
    | ~ spl3_6 ),
    inference(resolution,[],[f146,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f146,plain,
    ( ! [X5] :
        ( ~ r1_xboole_0(k1_tarski(sK0),X5)
        | r1_xboole_0(sK1,X5) )
    | ~ spl3_6 ),
    inference(resolution,[],[f61,f101])).

fof(f101,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f445,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r1_tarski(sK1,X0) )
    | ~ spl3_10 ),
    inference(superposition,[],[f186,f142])).

fof(f142,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_10
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f186,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f64,f59])).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f468,plain,
    ( spl3_32
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f467,f201,f140,f463])).

fof(f463,plain,
    ( spl3_32
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f201,plain,
    ( spl3_13
  <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f467,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f443,f316])).

fof(f316,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f148,f172])).

fof(f172,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f171,f60])).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f171,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f160,f55])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f160,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f56,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f148,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f49,f48])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f443,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_10
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f203,f142])).

fof(f203,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f201])).

fof(f435,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f434,f136,f87,f140])).

fof(f87,plain,
    ( spl3_4
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f136,plain,
    ( spl3_9
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f434,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f431,f137])).

fof(f137,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f431,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f133,f89])).

fof(f89,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f133,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f52,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f394,plain,
    ( spl3_27
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f362,f174,f391])).

fof(f391,plain,
    ( spl3_27
  <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f174,plain,
    ( spl3_11
  <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f362,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(superposition,[],[f152,f176])).

fof(f176,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f152,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f49,f48])).

fof(f312,plain,
    ( spl3_2
    | ~ spl3_23 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl3_2
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f309,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f309,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_23 ),
    inference(resolution,[],[f306,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f306,plain,
    ( r1_xboole_0(sK1,sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl3_23
  <=> r1_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f307,plain,
    ( spl3_23
    | ~ spl3_6
    | spl3_22 ),
    inference(avatar_split_clause,[],[f302,f298,f99,f304])).

fof(f298,plain,
    ( spl3_22
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f302,plain,
    ( r1_xboole_0(sK1,sK1)
    | ~ spl3_6
    | spl3_22 ),
    inference(resolution,[],[f300,f147])).

fof(f300,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f298])).

fof(f301,plain,
    ( ~ spl3_22
    | spl3_9 ),
    inference(avatar_split_clause,[],[f293,f136,f298])).

fof(f293,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_9 ),
    inference(resolution,[],[f186,f138])).

fof(f138,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f289,plain,
    ( spl3_20
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f265,f248,f277])).

fof(f277,plain,
    ( spl3_20
  <=> k5_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f248,plain,
    ( spl3_17
  <=> k5_xboole_0(sK1,sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f265,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))
    | ~ spl3_17 ),
    inference(superposition,[],[f54,f250])).

fof(f250,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f248])).

fof(f54,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f275,plain,
    ( ~ spl3_18
    | spl3_19
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f266,f248,f272,f268])).

fof(f272,plain,
    ( spl3_19
  <=> k1_tarski(sK0) = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f266,plain,
    ( k1_tarski(sK0) = k5_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f259,f172])).

fof(f259,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl3_17 ),
    inference(superposition,[],[f250,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f251,plain,
    ( spl3_17
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f246,f174,f248])).

fof(f246,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f245,f172])).

fof(f245,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f238,f54])).

fof(f238,plain,
    ( k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0)
    | ~ spl3_11 ),
    inference(superposition,[],[f192,f48])).

fof(f192,plain,
    ( ! [X0] : k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_tarski(sK0),X0)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0)
    | ~ spl3_11 ),
    inference(superposition,[],[f49,f176])).

fof(f213,plain,
    ( spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f194,f174,f201])).

fof(f194,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(superposition,[],[f54,f176])).

fof(f177,plain,
    ( spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f165,f87,f174])).

fof(f165,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f56,f89])).

fof(f122,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f111,f87,f118,f114])).

fof(f118,plain,
    ( spl3_8
  <=> sK2 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f111,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f89,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f102,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f96,f87,f99])).

fof(f96,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f57,f89])).

fof(f90,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f40,f87])).

fof(f40,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f85,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f82])).

fof(f82,plain,
    ( spl3_3
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f41,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f77])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43,f72])).

fof(f72,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (2092)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.49  % (2084)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.49  % (2090)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.51  % (2081)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (2098)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.52  % (2106)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.52  % (2080)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.53  % (2106)Refutation not found, incomplete strategy% (2106)------------------------------
% 0.19/0.53  % (2106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2106)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (2106)Memory used [KB]: 1663
% 0.19/0.53  % (2106)Time elapsed: 0.112 s
% 0.19/0.53  % (2106)------------------------------
% 0.19/0.53  % (2106)------------------------------
% 0.19/0.53  % (2078)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.53  % (2102)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.53  % (2088)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.53  % (2078)Refutation not found, incomplete strategy% (2078)------------------------------
% 0.19/0.53  % (2078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2078)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (2078)Memory used [KB]: 1663
% 0.19/0.53  % (2078)Time elapsed: 0.114 s
% 0.19/0.53  % (2078)------------------------------
% 0.19/0.53  % (2078)------------------------------
% 0.19/0.53  % (2082)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.53  % (2079)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.54  % (2093)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.54  % (2104)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.54  % (2103)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (2105)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.54  % (2094)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.54  % (2085)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.54  % (2093)Refutation not found, incomplete strategy% (2093)------------------------------
% 0.19/0.54  % (2093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (2101)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.54  % (2096)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.54  % (2093)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (2093)Memory used [KB]: 10618
% 0.19/0.54  % (2093)Time elapsed: 0.138 s
% 0.19/0.54  % (2093)------------------------------
% 0.19/0.54  % (2093)------------------------------
% 0.19/0.55  % (2095)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.55  % (2097)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.55  % (2086)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.55  % (2099)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.55  % (2089)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.55  % (2089)Refutation not found, incomplete strategy% (2089)------------------------------
% 0.19/0.55  % (2089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (2089)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.55  
% 0.19/0.55  % (2089)Memory used [KB]: 10618
% 0.19/0.55  % (2089)Time elapsed: 0.142 s
% 0.19/0.55  % (2089)------------------------------
% 0.19/0.55  % (2089)------------------------------
% 0.19/0.55  % (2087)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.55  % (2091)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.53/0.56  % (2100)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.53/0.56  % (2083)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.57  % (2077)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.53/0.57  % (2098)Refutation found. Thanks to Tanya!
% 1.53/0.57  % SZS status Theorem for theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f1056,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f102,f122,f177,f213,f251,f275,f289,f301,f307,f312,f394,f435,f468,f1052,f1053,f1055])).
% 1.53/0.57  fof(f1055,plain,(
% 1.53/0.57    k1_tarski(sK0) != k5_xboole_0(sK1,sK2) | k5_xboole_0(sK1,sK2) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) | k1_xboole_0 != k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))) | k3_xboole_0(sK1,sK2) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) | sK2 != k3_xboole_0(sK1,sK2) | k1_xboole_0 = sK2),
% 1.53/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.57  fof(f1053,plain,(
% 1.53/0.57    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0) | sK1 = sK2),
% 1.53/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.53/0.57  fof(f1052,plain,(
% 1.53/0.57    ~spl3_6 | spl3_7 | ~spl3_10 | spl3_18),
% 1.53/0.57    inference(avatar_contradiction_clause,[],[f1051])).
% 1.53/0.57  fof(f1051,plain,(
% 1.53/0.57    $false | (~spl3_6 | spl3_7 | ~spl3_10 | spl3_18)),
% 1.53/0.57    inference(subsumption_resolution,[],[f1045,f270])).
% 1.53/0.57  fof(f270,plain,(
% 1.53/0.57    ~r1_xboole_0(sK1,sK2) | spl3_18),
% 1.53/0.57    inference(avatar_component_clause,[],[f268])).
% 1.53/0.57  fof(f268,plain,(
% 1.53/0.57    spl3_18 <=> r1_xboole_0(sK1,sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.53/0.57  fof(f1045,plain,(
% 1.53/0.57    r1_xboole_0(sK1,sK2) | (~spl3_6 | spl3_7 | ~spl3_10)),
% 1.53/0.57    inference(resolution,[],[f746,f116])).
% 1.53/0.57  fof(f116,plain,(
% 1.53/0.57    ~r1_tarski(sK1,sK2) | spl3_7),
% 1.53/0.57    inference(avatar_component_clause,[],[f114])).
% 1.53/0.57  fof(f114,plain,(
% 1.53/0.57    spl3_7 <=> r1_tarski(sK1,sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.53/0.57  fof(f746,plain,(
% 1.53/0.57    ( ! [X0] : (r1_tarski(sK1,X0) | r1_xboole_0(sK1,X0)) ) | (~spl3_6 | ~spl3_10)),
% 1.53/0.57    inference(resolution,[],[f445,f147])).
% 1.53/0.57  fof(f147,plain,(
% 1.53/0.57    ( ! [X0] : (r2_hidden(sK0,X0) | r1_xboole_0(sK1,X0)) ) | ~spl3_6),
% 1.53/0.57    inference(resolution,[],[f146,f58])).
% 1.53/0.57  fof(f58,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f30])).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f20])).
% 1.53/0.57  fof(f20,axiom,(
% 1.53/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.53/0.57  fof(f146,plain,(
% 1.53/0.57    ( ! [X5] : (~r1_xboole_0(k1_tarski(sK0),X5) | r1_xboole_0(sK1,X5)) ) | ~spl3_6),
% 1.53/0.57    inference(resolution,[],[f61,f101])).
% 1.53/0.57  fof(f101,plain,(
% 1.53/0.57    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_6),
% 1.53/0.57    inference(avatar_component_clause,[],[f99])).
% 1.53/0.57  fof(f99,plain,(
% 1.53/0.57    spl3_6 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.53/0.57  fof(f61,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f32])).
% 1.53/0.57  fof(f32,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.53/0.57    inference(flattening,[],[f31])).
% 1.53/0.57  fof(f31,plain,(
% 1.53/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.53/0.57  fof(f445,plain,(
% 1.53/0.57    ( ! [X0] : (~r2_hidden(sK0,X0) | r1_tarski(sK1,X0)) ) | ~spl3_10),
% 1.53/0.57    inference(superposition,[],[f186,f142])).
% 1.53/0.57  fof(f142,plain,(
% 1.53/0.57    sK1 = k1_tarski(sK0) | ~spl3_10),
% 1.53/0.57    inference(avatar_component_clause,[],[f140])).
% 1.53/0.57  fof(f140,plain,(
% 1.53/0.57    spl3_10 <=> sK1 = k1_tarski(sK0)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.53/0.57  fof(f186,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f185])).
% 1.53/0.57  fof(f185,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(superposition,[],[f64,f59])).
% 1.53/0.57  fof(f59,plain,(
% 1.53/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,axiom,(
% 1.53/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.57  fof(f64,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f39])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.53/0.57    inference(flattening,[],[f38])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.53/0.57    inference(nnf_transformation,[],[f22])).
% 1.53/0.57  fof(f22,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.53/0.57  fof(f468,plain,(
% 1.53/0.57    spl3_32 | ~spl3_10 | ~spl3_13),
% 1.53/0.57    inference(avatar_split_clause,[],[f467,f201,f140,f463])).
% 1.53/0.57  fof(f463,plain,(
% 1.53/0.57    spl3_32 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.53/0.57  fof(f201,plain,(
% 1.53/0.57    spl3_13 <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2))),
% 1.53/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.53/0.57  fof(f467,plain,(
% 1.53/0.57    sK2 = k3_xboole_0(sK1,sK2) | (~spl3_10 | ~spl3_13)),
% 1.53/0.57    inference(forward_demodulation,[],[f443,f316])).
% 1.53/0.57  fof(f316,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.53/0.57    inference(forward_demodulation,[],[f148,f172])).
% 1.53/0.57  fof(f172,plain,(
% 1.53/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.53/0.57    inference(forward_demodulation,[],[f171,f60])).
% 1.53/0.57  fof(f60,plain,(
% 1.53/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f26])).
% 1.53/0.57  fof(f26,plain,(
% 1.53/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.57    inference(rectify,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.53/0.57  fof(f171,plain,(
% 1.53/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.53/0.57    inference(forward_demodulation,[],[f160,f55])).
% 1.53/0.57  fof(f55,plain,(
% 1.53/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.53/0.57    inference(cnf_transformation,[],[f25])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.53/0.57    inference(rectify,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.67/0.57  fof(f160,plain,(
% 1.67/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.67/0.57    inference(superposition,[],[f56,f48])).
% 1.67/0.57  fof(f48,plain,(
% 1.67/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f11])).
% 1.67/0.57  fof(f11,axiom,(
% 1.67/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.67/0.57  fof(f56,plain,(
% 1.67/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.67/0.57    inference(cnf_transformation,[],[f12])).
% 1.67/0.57  fof(f12,axiom,(
% 1.67/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.67/0.57  fof(f148,plain,(
% 1.67/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.67/0.57    inference(superposition,[],[f49,f48])).
% 1.67/0.57  fof(f49,plain,(
% 1.67/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.67/0.57    inference(cnf_transformation,[],[f10])).
% 1.67/0.57  fof(f10,axiom,(
% 1.67/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.67/0.57  fof(f443,plain,(
% 1.67/0.57    k3_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | (~spl3_10 | ~spl3_13)),
% 1.67/0.57    inference(backward_demodulation,[],[f203,f142])).
% 1.67/0.57  fof(f203,plain,(
% 1.67/0.57    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) | ~spl3_13),
% 1.67/0.57    inference(avatar_component_clause,[],[f201])).
% 1.67/0.57  fof(f435,plain,(
% 1.67/0.57    spl3_10 | ~spl3_4 | ~spl3_9),
% 1.67/0.57    inference(avatar_split_clause,[],[f434,f136,f87,f140])).
% 1.67/0.57  fof(f87,plain,(
% 1.67/0.57    spl3_4 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.67/0.57  fof(f136,plain,(
% 1.67/0.57    spl3_9 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.67/0.57  fof(f434,plain,(
% 1.67/0.57    sK1 = k1_tarski(sK0) | (~spl3_4 | ~spl3_9)),
% 1.67/0.57    inference(subsumption_resolution,[],[f431,f137])).
% 1.67/0.57  fof(f137,plain,(
% 1.67/0.57    r1_tarski(k1_tarski(sK0),sK1) | ~spl3_9),
% 1.67/0.57    inference(avatar_component_clause,[],[f136])).
% 1.67/0.57  fof(f431,plain,(
% 1.67/0.57    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0) | ~spl3_4),
% 1.67/0.57    inference(superposition,[],[f133,f89])).
% 1.67/0.57  fof(f89,plain,(
% 1.67/0.57    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl3_4),
% 1.67/0.57    inference(avatar_component_clause,[],[f87])).
% 1.67/0.57  fof(f133,plain,(
% 1.67/0.57    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 1.67/0.57    inference(resolution,[],[f52,f57])).
% 1.67/0.57  fof(f57,plain,(
% 1.67/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.67/0.57    inference(cnf_transformation,[],[f9])).
% 1.67/0.57  fof(f9,axiom,(
% 1.67/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.67/0.57  fof(f52,plain,(
% 1.67/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f37])).
% 1.67/0.57  fof(f37,plain,(
% 1.67/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.67/0.57    inference(flattening,[],[f36])).
% 1.67/0.57  fof(f36,plain,(
% 1.67/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.67/0.57    inference(nnf_transformation,[],[f5])).
% 1.67/0.57  fof(f5,axiom,(
% 1.67/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.67/0.57  fof(f394,plain,(
% 1.67/0.57    spl3_27 | ~spl3_11),
% 1.67/0.57    inference(avatar_split_clause,[],[f362,f174,f391])).
% 1.67/0.57  fof(f391,plain,(
% 1.67/0.57    spl3_27 <=> k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.67/0.57  fof(f174,plain,(
% 1.67/0.57    spl3_11 <=> k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.67/0.57  fof(f362,plain,(
% 1.67/0.57    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))) | ~spl3_11),
% 1.67/0.57    inference(superposition,[],[f152,f176])).
% 1.67/0.57  fof(f176,plain,(
% 1.67/0.57    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) | ~spl3_11),
% 1.67/0.57    inference(avatar_component_clause,[],[f174])).
% 1.67/0.57  fof(f152,plain,(
% 1.67/0.57    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 1.67/0.57    inference(superposition,[],[f49,f48])).
% 1.67/0.57  fof(f312,plain,(
% 1.67/0.57    spl3_2 | ~spl3_23),
% 1.67/0.57    inference(avatar_contradiction_clause,[],[f311])).
% 1.67/0.57  fof(f311,plain,(
% 1.67/0.57    $false | (spl3_2 | ~spl3_23)),
% 1.67/0.57    inference(subsumption_resolution,[],[f309,f79])).
% 1.67/0.57  fof(f79,plain,(
% 1.67/0.57    k1_xboole_0 != sK1 | spl3_2),
% 1.67/0.57    inference(avatar_component_clause,[],[f77])).
% 1.67/0.57  fof(f77,plain,(
% 1.67/0.57    spl3_2 <=> k1_xboole_0 = sK1),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.67/0.57  fof(f309,plain,(
% 1.67/0.57    k1_xboole_0 = sK1 | ~spl3_23),
% 1.67/0.57    inference(resolution,[],[f306,f47])).
% 1.67/0.57  fof(f47,plain,(
% 1.67/0.57    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.67/0.57    inference(cnf_transformation,[],[f28])).
% 1.67/0.57  fof(f28,plain,(
% 1.67/0.57    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.67/0.57    inference(ennf_transformation,[],[f8])).
% 1.67/0.57  fof(f8,axiom,(
% 1.67/0.57    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.67/0.57  fof(f306,plain,(
% 1.67/0.57    r1_xboole_0(sK1,sK1) | ~spl3_23),
% 1.67/0.57    inference(avatar_component_clause,[],[f304])).
% 1.67/0.57  fof(f304,plain,(
% 1.67/0.57    spl3_23 <=> r1_xboole_0(sK1,sK1)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.67/0.57  fof(f307,plain,(
% 1.67/0.57    spl3_23 | ~spl3_6 | spl3_22),
% 1.67/0.57    inference(avatar_split_clause,[],[f302,f298,f99,f304])).
% 1.67/0.57  fof(f298,plain,(
% 1.67/0.57    spl3_22 <=> r2_hidden(sK0,sK1)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.67/0.57  fof(f302,plain,(
% 1.67/0.57    r1_xboole_0(sK1,sK1) | (~spl3_6 | spl3_22)),
% 1.67/0.57    inference(resolution,[],[f300,f147])).
% 1.67/0.57  fof(f300,plain,(
% 1.67/0.57    ~r2_hidden(sK0,sK1) | spl3_22),
% 1.67/0.57    inference(avatar_component_clause,[],[f298])).
% 1.67/0.57  fof(f301,plain,(
% 1.67/0.57    ~spl3_22 | spl3_9),
% 1.67/0.57    inference(avatar_split_clause,[],[f293,f136,f298])).
% 1.67/0.57  fof(f293,plain,(
% 1.67/0.57    ~r2_hidden(sK0,sK1) | spl3_9),
% 1.67/0.57    inference(resolution,[],[f186,f138])).
% 1.67/0.57  fof(f138,plain,(
% 1.67/0.57    ~r1_tarski(k1_tarski(sK0),sK1) | spl3_9),
% 1.67/0.57    inference(avatar_component_clause,[],[f136])).
% 1.67/0.57  fof(f289,plain,(
% 1.67/0.57    spl3_20 | ~spl3_17),
% 1.67/0.57    inference(avatar_split_clause,[],[f265,f248,f277])).
% 1.67/0.57  fof(f277,plain,(
% 1.67/0.57    spl3_20 <=> k5_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.67/0.57  fof(f248,plain,(
% 1.67/0.57    spl3_17 <=> k5_xboole_0(sK1,sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.67/0.57  fof(f265,plain,(
% 1.67/0.57    k5_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) | ~spl3_17),
% 1.67/0.57    inference(superposition,[],[f54,f250])).
% 1.67/0.57  fof(f250,plain,(
% 1.67/0.57    k5_xboole_0(sK1,sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0)) | ~spl3_17),
% 1.67/0.57    inference(avatar_component_clause,[],[f248])).
% 1.67/0.57  fof(f54,plain,(
% 1.67/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f1])).
% 1.67/0.57  fof(f1,axiom,(
% 1.67/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.67/0.57  fof(f275,plain,(
% 1.67/0.57    ~spl3_18 | spl3_19 | ~spl3_17),
% 1.67/0.57    inference(avatar_split_clause,[],[f266,f248,f272,f268])).
% 1.67/0.57  fof(f272,plain,(
% 1.67/0.57    spl3_19 <=> k1_tarski(sK0) = k5_xboole_0(sK1,sK2)),
% 1.67/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.67/0.57  fof(f266,plain,(
% 1.67/0.57    k1_tarski(sK0) = k5_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK2) | ~spl3_17),
% 1.67/0.57    inference(forward_demodulation,[],[f259,f172])).
% 1.67/0.57  fof(f259,plain,(
% 1.67/0.57    k5_xboole_0(sK1,sK2) = k5_xboole_0(k1_xboole_0,k1_tarski(sK0)) | ~r1_xboole_0(sK1,sK2) | ~spl3_17),
% 1.67/0.57    inference(superposition,[],[f250,f44])).
% 1.67/0.57  fof(f44,plain,(
% 1.67/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.67/0.57    inference(cnf_transformation,[],[f35])).
% 1.67/0.57  fof(f35,plain,(
% 1.67/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.67/0.57    inference(nnf_transformation,[],[f2])).
% 1.67/0.57  fof(f2,axiom,(
% 1.67/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.67/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.67/0.57  fof(f251,plain,(
% 1.67/0.57    spl3_17 | ~spl3_11),
% 1.67/0.57    inference(avatar_split_clause,[],[f246,f174,f248])).
% 1.67/0.57  fof(f246,plain,(
% 1.67/0.57    k5_xboole_0(sK1,sK2) = k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0)) | ~spl3_11),
% 1.67/0.57    inference(forward_demodulation,[],[f245,f172])).
% 1.67/0.57  fof(f245,plain,(
% 1.67/0.57    k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,sK2)) | ~spl3_11),
% 1.67/0.57    inference(forward_demodulation,[],[f238,f54])).
% 1.67/0.58  fof(f238,plain,(
% 1.67/0.58    k5_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) | ~spl3_11),
% 1.67/0.58    inference(superposition,[],[f192,f48])).
% 1.67/0.58  fof(f192,plain,(
% 1.67/0.58    ( ! [X0] : (k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k1_tarski(sK0),X0)) = k5_xboole_0(k3_xboole_0(sK1,sK2),X0)) ) | ~spl3_11),
% 1.67/0.58    inference(superposition,[],[f49,f176])).
% 1.67/0.58  fof(f213,plain,(
% 1.67/0.58    spl3_13 | ~spl3_11),
% 1.67/0.58    inference(avatar_split_clause,[],[f194,f174,f201])).
% 1.67/0.58  fof(f194,plain,(
% 1.67/0.58    k3_xboole_0(sK1,sK2) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,sK2)) | ~spl3_11),
% 1.67/0.58    inference(superposition,[],[f54,f176])).
% 1.67/0.58  fof(f177,plain,(
% 1.67/0.58    spl3_11 | ~spl3_4),
% 1.67/0.58    inference(avatar_split_clause,[],[f165,f87,f174])).
% 1.67/0.58  fof(f165,plain,(
% 1.67/0.58    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) | ~spl3_4),
% 1.67/0.58    inference(superposition,[],[f56,f89])).
% 1.67/0.58  fof(f122,plain,(
% 1.67/0.58    ~spl3_7 | spl3_8 | ~spl3_4),
% 1.67/0.58    inference(avatar_split_clause,[],[f111,f87,f118,f114])).
% 1.67/0.58  fof(f118,plain,(
% 1.67/0.58    spl3_8 <=> sK2 = k1_tarski(sK0)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.67/0.58  fof(f111,plain,(
% 1.67/0.58    sK2 = k1_tarski(sK0) | ~r1_tarski(sK1,sK2) | ~spl3_4),
% 1.67/0.58    inference(superposition,[],[f89,f53])).
% 1.67/0.58  fof(f53,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f29])).
% 1.67/0.58  fof(f29,plain,(
% 1.67/0.58    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.67/0.58    inference(ennf_transformation,[],[f6])).
% 1.67/0.58  fof(f6,axiom,(
% 1.67/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.67/0.58  fof(f102,plain,(
% 1.67/0.58    spl3_6 | ~spl3_4),
% 1.67/0.58    inference(avatar_split_clause,[],[f96,f87,f99])).
% 1.67/0.58  fof(f96,plain,(
% 1.67/0.58    r1_tarski(sK1,k1_tarski(sK0)) | ~spl3_4),
% 1.67/0.58    inference(superposition,[],[f57,f89])).
% 1.67/0.58  fof(f90,plain,(
% 1.67/0.58    spl3_4),
% 1.67/0.58    inference(avatar_split_clause,[],[f40,f87])).
% 1.67/0.58  fof(f40,plain,(
% 1.67/0.58    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.67/0.58    inference(cnf_transformation,[],[f34])).
% 1.67/0.58  fof(f34,plain,(
% 1.67/0.58    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f33])).
% 1.67/0.58  fof(f33,plain,(
% 1.67/0.58    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f27,plain,(
% 1.67/0.58    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.67/0.58    inference(ennf_transformation,[],[f24])).
% 1.67/0.58  fof(f24,negated_conjecture,(
% 1.67/0.58    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.67/0.58    inference(negated_conjecture,[],[f23])).
% 1.67/0.58  fof(f23,conjecture,(
% 1.67/0.58    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.67/0.58  fof(f85,plain,(
% 1.67/0.58    ~spl3_3),
% 1.67/0.58    inference(avatar_split_clause,[],[f41,f82])).
% 1.67/0.58  fof(f82,plain,(
% 1.67/0.58    spl3_3 <=> sK1 = sK2),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.67/0.58  fof(f41,plain,(
% 1.67/0.58    sK1 != sK2),
% 1.67/0.58    inference(cnf_transformation,[],[f34])).
% 1.67/0.58  fof(f80,plain,(
% 1.67/0.58    ~spl3_2),
% 1.67/0.58    inference(avatar_split_clause,[],[f42,f77])).
% 1.67/0.58  fof(f42,plain,(
% 1.67/0.58    k1_xboole_0 != sK1),
% 1.67/0.58    inference(cnf_transformation,[],[f34])).
% 1.67/0.58  fof(f75,plain,(
% 1.67/0.58    ~spl3_1),
% 1.67/0.58    inference(avatar_split_clause,[],[f43,f72])).
% 1.67/0.58  fof(f72,plain,(
% 1.67/0.58    spl3_1 <=> k1_xboole_0 = sK2),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.67/0.58  fof(f43,plain,(
% 1.67/0.58    k1_xboole_0 != sK2),
% 1.67/0.58    inference(cnf_transformation,[],[f34])).
% 1.67/0.58  % SZS output end Proof for theBenchmark
% 1.67/0.58  % (2098)------------------------------
% 1.67/0.58  % (2098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (2098)Termination reason: Refutation
% 1.67/0.58  
% 1.67/0.58  % (2098)Memory used [KB]: 7164
% 1.67/0.58  % (2098)Time elapsed: 0.153 s
% 1.67/0.58  % (2098)------------------------------
% 1.67/0.58  % (2098)------------------------------
% 1.67/0.58  % (2076)Success in time 0.22 s
%------------------------------------------------------------------------------
