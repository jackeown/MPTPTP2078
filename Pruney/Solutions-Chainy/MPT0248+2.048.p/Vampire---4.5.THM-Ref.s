%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:56 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 512 expanded)
%              Number of leaves         :   41 ( 208 expanded)
%              Depth                    :   16
%              Number of atoms          :  518 (1263 expanded)
%              Number of equality atoms :  160 ( 466 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2950,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f84,f98,f103,f115,f138,f187,f245,f261,f266,f271,f277,f452,f475,f620,f1360,f1435,f1637,f1665,f1834,f1875,f2474,f2570,f2625,f2682,f2686,f2902])).

fof(f2902,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f2901])).

fof(f2901,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(global_subsumption,[],[f33,f91,f2788])).

fof(f2788,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f376,f543])).

fof(f543,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(resolution,[],[f507,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f507,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(resolution,[],[f482,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f482,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f481,f451])).

fof(f451,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl5_26
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f481,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k1_xboole_0,k1_tarski(sK0)))
    | ~ spl5_28 ),
    inference(resolution,[],[f474,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f474,plain,
    ( r1_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f472])).

fof(f472,plain,
    ( spl5_28
  <=> r1_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f376,plain,
    ( k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f71,f91])).

fof(f71,plain,
    ( k1_tarski(sK0) = k2_xboole_0(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_1
  <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f91,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f2686,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1)
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2682,plain,
    ( spl5_2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_51 ),
    inference(avatar_contradiction_clause,[],[f2681])).

fof(f2681,plain,
    ( $false
    | spl5_2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f2680,f79])).

fof(f79,plain,
    ( k1_xboole_0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2680,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3
    | spl5_6
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f2677,f97])).

fof(f97,plain,
    ( sK1 != sK2
    | spl5_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl5_6
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f2677,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | ~ spl5_3
    | ~ spl5_51 ),
    inference(resolution,[],[f2624,f531])).

fof(f531,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl5_3 ),
    inference(superposition,[],[f55,f82])).

fof(f82,plain,
    ( sK1 = k1_tarski(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_3
  <=> sK1 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f2624,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f2622])).

fof(f2622,plain,
    ( spl5_51
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f2625,plain,
    ( spl5_51
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f2596,f2567,f2622])).

fof(f2567,plain,
    ( spl5_50
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f2596,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_50 ),
    inference(superposition,[],[f39,f2569])).

fof(f2569,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f2567])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2570,plain,
    ( spl5_50
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f2530,f2471,f472,f449,f2567])).

fof(f2471,plain,
    ( spl5_49
  <=> sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f2530,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_49 ),
    inference(superposition,[],[f2473,f716])).

fof(f716,plain,
    ( ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f712,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f712,plain,
    ( ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(superposition,[],[f44,f652])).

fof(f652,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(superposition,[],[f542,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f542,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(resolution,[],[f507,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2473,plain,
    ( sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f2471])).

fof(f2474,plain,
    ( spl5_49
    | ~ spl5_45
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f2048,f1872,f1831,f2471])).

fof(f1831,plain,
    ( spl5_45
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f1872,plain,
    ( spl5_46
  <=> sK1 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f2048,plain,
    ( sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl5_45
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f2047,f1874])).

fof(f1874,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f1872])).

fof(f2047,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl5_45 ),
    inference(forward_demodulation,[],[f2032,f41])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f2032,plain,
    ( k5_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl5_45 ),
    inference(superposition,[],[f45,f1833])).

fof(f1833,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f1831])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f1875,plain,
    ( spl5_46
    | ~ spl5_3
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f1696,f1353,f472,f449,f268,f263,f90,f81,f1872])).

fof(f263,plain,
    ( spl5_18
  <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f268,plain,
    ( spl5_19
  <=> sK1 = k2_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1353,plain,
    ( spl5_37
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f1696,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl5_3
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f1361,f92])).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | spl5_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f1361,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_37 ),
    inference(backward_demodulation,[],[f1327,f1355])).

fof(f1355,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f1353])).

fof(f1327,plain,
    ( sK1 = k3_xboole_0(sK1,sK2)
    | sK1 = k5_xboole_0(sK1,sK2)
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f1326,f40])).

fof(f1326,plain,
    ( sK1 = k5_xboole_0(sK1,sK2)
    | sK1 = k3_xboole_0(sK2,sK1)
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f1297,f716])).

fof(f1297,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | sK1 = k3_xboole_0(sK2,sK1)
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(superposition,[],[f265,f897])).

fof(f897,plain,
    ( ! [X9] :
        ( k1_xboole_0 = k3_xboole_0(sK1,X9)
        | sK1 = k3_xboole_0(X9,sK1) )
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(superposition,[],[f40,f631])).

fof(f631,plain,
    ( ! [X0] :
        ( sK1 = k3_xboole_0(sK1,X0)
        | k1_xboole_0 = k3_xboole_0(sK1,X0) )
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(resolution,[],[f297,f531])).

fof(f297,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),sK1)
    | ~ spl5_19 ),
    inference(superposition,[],[f58,f270])).

fof(f270,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f268])).

fof(f58,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f265,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f263])).

fof(f1834,plain,
    ( spl5_45
    | ~ spl5_3
    | spl5_5
    | ~ spl5_11
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f1386,f1353,f145,f90,f81,f1831])).

fof(f145,plain,
    ( spl5_11
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1386,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_3
    | spl5_5
    | ~ spl5_11
    | ~ spl5_37 ),
    inference(subsumption_resolution,[],[f1366,f92])).

fof(f1366,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_37 ),
    inference(superposition,[],[f1355,f753])).

fof(f753,plain,
    ( ! [X6] :
        ( sK1 = k3_xboole_0(sK1,X6)
        | k1_xboole_0 = k3_xboole_0(X6,sK1) )
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(superposition,[],[f40,f595])).

fof(f595,plain,
    ( ! [X0] :
        ( sK1 = k3_xboole_0(X0,sK1)
        | k1_xboole_0 = k3_xboole_0(X0,sK1) )
    | ~ spl5_3
    | ~ spl5_11 ),
    inference(resolution,[],[f531,f252])).

fof(f252,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,sK1),sK1)
    | ~ spl5_11 ),
    inference(superposition,[],[f180,f40])).

fof(f180,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),sK1)
    | ~ spl5_11 ),
    inference(superposition,[],[f58,f147])).

fof(f147,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f1665,plain,
    ( spl5_6
    | ~ spl5_11
    | ~ spl5_43 ),
    inference(avatar_contradiction_clause,[],[f1664])).

fof(f1664,plain,
    ( $false
    | spl5_6
    | ~ spl5_11
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f1663,f97])).

fof(f1663,plain,
    ( sK1 = sK2
    | ~ spl5_11
    | ~ spl5_43 ),
    inference(forward_demodulation,[],[f1662,f147])).

fof(f1662,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl5_43 ),
    inference(resolution,[],[f1636,f48])).

fof(f1636,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f1634])).

fof(f1634,plain,
    ( spl5_43
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f1637,plain,
    ( spl5_43
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f1605,f1432,f472,f449,f1634])).

fof(f1432,plain,
    ( spl5_41
  <=> sK1 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f1605,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_41 ),
    inference(superposition,[],[f1163,f1434])).

fof(f1434,plain,
    ( sK1 = k3_xboole_0(sK1,sK2)
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f1432])).

fof(f1163,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0)
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(superposition,[],[f1089,f40])).

fof(f1089,plain,
    ( ! [X2,X1] : r1_tarski(k3_xboole_0(X1,X2),X1)
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(superposition,[],[f58,f1026])).

fof(f1026,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(superposition,[],[f715,f716])).

fof(f715,plain,
    ( ! [X5] : k4_xboole_0(k2_xboole_0(X5,k1_xboole_0),k1_xboole_0) = X5
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f711,f37])).

fof(f711,plain,
    ( ! [X5] : k5_xboole_0(X5,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X5,k1_xboole_0),k1_xboole_0)
    | ~ spl5_26
    | ~ spl5_28 ),
    inference(superposition,[],[f45,f652])).

fof(f1435,plain,
    ( spl5_41
    | ~ spl5_3
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f1410,f1357,f472,f449,f268,f263,f90,f81,f1432])).

fof(f1357,plain,
    ( spl5_38
  <=> k1_xboole_0 = k5_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f1410,plain,
    ( sK1 = k3_xboole_0(sK1,sK2)
    | ~ spl5_3
    | spl5_5
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f1407,f92])).

fof(f1407,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_xboole_0(sK1,sK2)
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_26
    | ~ spl5_28
    | ~ spl5_38 ),
    inference(backward_demodulation,[],[f1327,f1359])).

fof(f1359,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK2)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f1357])).

fof(f1360,plain,
    ( spl5_37
    | spl5_38
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f911,f617,f268,f263,f81,f1357,f1353])).

fof(f617,plain,
    ( spl5_32
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f911,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,sK2)
    | k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f894,f619])).

fof(f619,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f617])).

fof(f894,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_19 ),
    inference(superposition,[],[f265,f631])).

fof(f620,plain,
    ( spl5_32
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f295,f268,f258,f617])).

fof(f258,plain,
    ( spl5_17
  <=> sK1 = k3_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f295,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f294,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f294,plain,
    ( k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl5_17
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f292,f270])).

fof(f292,plain,
    ( k5_xboole_0(sK1,sK1) = k4_xboole_0(k2_xboole_0(sK1,sK1),sK1)
    | ~ spl5_17 ),
    inference(superposition,[],[f45,f260])).

fof(f260,plain,
    ( sK1 = k3_xboole_0(sK1,sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f258])).

fof(f475,plain,
    ( spl5_28
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f463,f449,f472])).

fof(f463,plain,
    ( r1_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl5_26 ),
    inference(trivial_inequality_removal,[],[f460])).

fof(f460,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl5_26 ),
    inference(superposition,[],[f50,f451])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f452,plain,
    ( spl5_26
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f382,f100,f90,f449])).

fof(f100,plain,
    ( spl5_7
  <=> r1_tarski(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f382,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f105,f91])).

fof(f105,plain,
    ( sK1 = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl5_7 ),
    inference(resolution,[],[f102,f49])).

fof(f102,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f277,plain,
    ( spl5_20
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f226,f184,f274])).

fof(f274,plain,
    ( spl5_20
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f184,plain,
    ( spl5_13
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f226,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)
    | ~ spl5_13 ),
    inference(resolution,[],[f186,f49])).

fof(f186,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f184])).

fof(f271,plain,
    ( spl5_19
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f175,f135,f268])).

fof(f135,plain,
    ( spl5_10
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f175,plain,
    ( sK1 = k2_xboole_0(sK1,sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f137,f48])).

fof(f137,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f135])).

fof(f266,plain,
    ( spl5_18
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f241,f81,f69,f263])).

fof(f241,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f75,f82])).

fof(f75,plain,
    ( k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2))
    | ~ spl5_1 ),
    inference(superposition,[],[f45,f71])).

fof(f261,plain,
    ( spl5_17
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f174,f135,f258])).

fof(f174,plain,
    ( sK1 = k3_xboole_0(sK1,sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f137,f49])).

fof(f245,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f127,f81,f69,f145])).

fof(f127,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f71,f82])).

fof(f187,plain,
    ( spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f141,f81,f184])).

fof(f141,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl5_3 ),
    inference(superposition,[],[f66,f82])).

fof(f66,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f138,plain,
    ( spl5_10
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f131,f100,f81,f135])).

fof(f131,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl5_3
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f102,f82])).

fof(f115,plain,
    ( spl5_5
    | spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f107,f100,f81,f90])).

fof(f107,plain,
    ( k1_xboole_0 = sK1
    | spl5_3
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f104,f83])).

fof(f83,plain,
    ( sK1 != k1_tarski(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f104,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1
    | ~ spl5_7 ),
    inference(resolution,[],[f102,f55])).

fof(f103,plain,
    ( spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f74,f69,f100])).

fof(f74,plain,
    ( r1_tarski(sK1,k1_tarski(sK0))
    | ~ spl5_1 ),
    inference(superposition,[],[f39,f71])).

fof(f98,plain,
    ( ~ spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f67,f81,f95])).

fof(f67,plain,
    ( sK1 != k1_tarski(sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f34])).

fof(f34,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f32,f81,f77])).

fof(f32,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f35,f69])).

fof(f35,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:26:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (13188)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.55  % (13204)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.55  % (13196)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.55  % (13189)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.34/0.55  % (13197)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.56  % (13206)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.56  % (13208)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.53/0.56  % (13197)Refutation not found, incomplete strategy% (13197)------------------------------
% 1.53/0.56  % (13197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (13190)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.56  % (13197)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (13197)Memory used [KB]: 6140
% 1.53/0.56  % (13197)Time elapsed: 0.003 s
% 1.53/0.56  % (13197)------------------------------
% 1.53/0.56  % (13197)------------------------------
% 1.53/0.56  % (13202)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.53/0.56  % (13209)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.56  % (13211)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.53/0.56  % (13186)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.53/0.56  % (13192)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.53/0.56  % (13198)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.57  % (13207)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.57  % (13193)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.57  % (13203)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.53/0.57  % (13182)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.53/0.57  % (13200)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.53/0.57  % (13185)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.53/0.57  % (13195)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.57  % (13191)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.53/0.57  % (13184)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.58  % (13187)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.58  % (13205)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.53/0.58  % (13194)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.53/0.58  % (13201)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.58  % (13199)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.58  % (13199)Refutation not found, incomplete strategy% (13199)------------------------------
% 1.53/0.58  % (13199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (13199)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (13199)Memory used [KB]: 10618
% 1.53/0.58  % (13199)Time elapsed: 0.117 s
% 1.53/0.58  % (13199)------------------------------
% 1.53/0.58  % (13199)------------------------------
% 1.53/0.58  % (13210)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.53/0.58  % (13183)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.35/0.68  % (13192)Refutation not found, incomplete strategy% (13192)------------------------------
% 2.35/0.68  % (13192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.35/0.68  % (13192)Termination reason: Refutation not found, incomplete strategy
% 2.35/0.68  
% 2.35/0.68  % (13192)Memory used [KB]: 11769
% 2.35/0.68  % (13192)Time elapsed: 0.267 s
% 2.35/0.68  % (13192)------------------------------
% 2.35/0.68  % (13192)------------------------------
% 2.35/0.68  % (13227)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.35/0.70  % (13234)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.35/0.74  % (13202)Refutation found. Thanks to Tanya!
% 2.35/0.74  % SZS status Theorem for theBenchmark
% 2.79/0.76  % SZS output start Proof for theBenchmark
% 2.79/0.76  fof(f2950,plain,(
% 2.79/0.76    $false),
% 2.79/0.76    inference(avatar_sat_refutation,[],[f72,f84,f98,f103,f115,f138,f187,f245,f261,f266,f271,f277,f452,f475,f620,f1360,f1435,f1637,f1665,f1834,f1875,f2474,f2570,f2625,f2682,f2686,f2902])).
% 2.79/0.76  fof(f2902,plain,(
% 2.79/0.76    ~spl5_1 | ~spl5_5 | ~spl5_26 | ~spl5_28),
% 2.79/0.76    inference(avatar_contradiction_clause,[],[f2901])).
% 2.79/0.76  fof(f2901,plain,(
% 2.79/0.76    $false | (~spl5_1 | ~spl5_5 | ~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(global_subsumption,[],[f33,f91,f2788])).
% 2.79/0.76  fof(f2788,plain,(
% 2.79/0.76    sK2 = k1_tarski(sK0) | (~spl5_1 | ~spl5_5 | ~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(forward_demodulation,[],[f376,f543])).
% 2.79/0.76  fof(f543,plain,(
% 2.79/0.76    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(resolution,[],[f507,f48])).
% 2.79/0.76  fof(f48,plain,(
% 2.79/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.79/0.76    inference(cnf_transformation,[],[f29])).
% 2.79/0.76  fof(f29,plain,(
% 2.79/0.76    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.79/0.76    inference(ennf_transformation,[],[f8])).
% 2.79/0.76  fof(f8,axiom,(
% 2.79/0.76    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.79/0.76  fof(f507,plain,(
% 2.79/0.76    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(resolution,[],[f482,f53])).
% 2.79/0.76  fof(f53,plain,(
% 2.79/0.76    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.79/0.76    inference(cnf_transformation,[],[f31])).
% 2.79/0.76  fof(f31,plain,(
% 2.79/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.79/0.76    inference(ennf_transformation,[],[f3])).
% 2.79/0.76  fof(f3,axiom,(
% 2.79/0.76    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.79/0.76  fof(f482,plain,(
% 2.79/0.76    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(forward_demodulation,[],[f481,f451])).
% 2.79/0.76  fof(f451,plain,(
% 2.79/0.76    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) | ~spl5_26),
% 2.79/0.76    inference(avatar_component_clause,[],[f449])).
% 2.79/0.76  fof(f449,plain,(
% 2.79/0.76    spl5_26 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.79/0.76  fof(f481,plain,(
% 2.79/0.76    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k1_xboole_0,k1_tarski(sK0)))) ) | ~spl5_28),
% 2.79/0.76    inference(resolution,[],[f474,f46])).
% 2.79/0.76  fof(f46,plain,(
% 2.79/0.76    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.79/0.76    inference(cnf_transformation,[],[f28])).
% 2.79/0.76  fof(f28,plain,(
% 2.79/0.76    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.79/0.76    inference(ennf_transformation,[],[f26])).
% 2.79/0.76  fof(f26,plain,(
% 2.79/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.79/0.76    inference(rectify,[],[f5])).
% 2.79/0.76  fof(f5,axiom,(
% 2.79/0.76    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.79/0.76  fof(f474,plain,(
% 2.79/0.76    r1_xboole_0(k1_xboole_0,k1_tarski(sK0)) | ~spl5_28),
% 2.79/0.76    inference(avatar_component_clause,[],[f472])).
% 2.79/0.76  fof(f472,plain,(
% 2.79/0.76    spl5_28 <=> r1_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.79/0.76  fof(f376,plain,(
% 2.79/0.76    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) | (~spl5_1 | ~spl5_5)),
% 2.79/0.76    inference(backward_demodulation,[],[f71,f91])).
% 2.79/0.76  fof(f71,plain,(
% 2.79/0.76    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) | ~spl5_1),
% 2.79/0.76    inference(avatar_component_clause,[],[f69])).
% 2.79/0.76  fof(f69,plain,(
% 2.79/0.76    spl5_1 <=> k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.79/0.76  fof(f91,plain,(
% 2.79/0.76    k1_xboole_0 = sK1 | ~spl5_5),
% 2.79/0.76    inference(avatar_component_clause,[],[f90])).
% 2.79/0.76  fof(f90,plain,(
% 2.79/0.76    spl5_5 <=> k1_xboole_0 = sK1),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.79/0.76  fof(f33,plain,(
% 2.79/0.76    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 2.79/0.76    inference(cnf_transformation,[],[f27])).
% 2.79/0.76  fof(f27,plain,(
% 2.79/0.76    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.79/0.76    inference(ennf_transformation,[],[f25])).
% 2.79/0.76  fof(f25,negated_conjecture,(
% 2.79/0.76    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.79/0.76    inference(negated_conjecture,[],[f24])).
% 2.79/0.76  fof(f24,conjecture,(
% 2.79/0.76    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.79/0.76  fof(f2686,plain,(
% 2.79/0.76    sK1 != k1_tarski(sK0) | k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK1) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 2.79/0.76    introduced(theory_tautology_sat_conflict,[])).
% 2.79/0.76  fof(f2682,plain,(
% 2.79/0.76    spl5_2 | ~spl5_3 | spl5_6 | ~spl5_51),
% 2.79/0.76    inference(avatar_contradiction_clause,[],[f2681])).
% 2.79/0.76  fof(f2681,plain,(
% 2.79/0.76    $false | (spl5_2 | ~spl5_3 | spl5_6 | ~spl5_51)),
% 2.79/0.76    inference(subsumption_resolution,[],[f2680,f79])).
% 2.79/0.76  fof(f79,plain,(
% 2.79/0.76    k1_xboole_0 != sK2 | spl5_2),
% 2.79/0.76    inference(avatar_component_clause,[],[f77])).
% 2.79/0.76  fof(f77,plain,(
% 2.79/0.76    spl5_2 <=> k1_xboole_0 = sK2),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.79/0.76  fof(f2680,plain,(
% 2.79/0.76    k1_xboole_0 = sK2 | (~spl5_3 | spl5_6 | ~spl5_51)),
% 2.79/0.76    inference(subsumption_resolution,[],[f2677,f97])).
% 2.79/0.76  fof(f97,plain,(
% 2.79/0.76    sK1 != sK2 | spl5_6),
% 2.79/0.76    inference(avatar_component_clause,[],[f95])).
% 2.79/0.76  fof(f95,plain,(
% 2.79/0.76    spl5_6 <=> sK1 = sK2),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.79/0.76  fof(f2677,plain,(
% 2.79/0.76    sK1 = sK2 | k1_xboole_0 = sK2 | (~spl5_3 | ~spl5_51)),
% 2.79/0.76    inference(resolution,[],[f2624,f531])).
% 2.79/0.76  fof(f531,plain,(
% 2.79/0.76    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | ~spl5_3),
% 2.79/0.76    inference(superposition,[],[f55,f82])).
% 2.79/0.76  fof(f82,plain,(
% 2.79/0.76    sK1 = k1_tarski(sK0) | ~spl5_3),
% 2.79/0.76    inference(avatar_component_clause,[],[f81])).
% 2.79/0.76  fof(f81,plain,(
% 2.79/0.76    spl5_3 <=> sK1 = k1_tarski(sK0)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.79/0.76  fof(f55,plain,(
% 2.79/0.76    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 2.79/0.76    inference(cnf_transformation,[],[f22])).
% 2.79/0.76  fof(f22,axiom,(
% 2.79/0.76    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.79/0.76  fof(f2624,plain,(
% 2.79/0.76    r1_tarski(sK2,sK1) | ~spl5_51),
% 2.79/0.76    inference(avatar_component_clause,[],[f2622])).
% 2.79/0.76  fof(f2622,plain,(
% 2.79/0.76    spl5_51 <=> r1_tarski(sK2,sK1)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 2.79/0.76  fof(f2625,plain,(
% 2.79/0.76    spl5_51 | ~spl5_50),
% 2.79/0.76    inference(avatar_split_clause,[],[f2596,f2567,f2622])).
% 2.79/0.76  fof(f2567,plain,(
% 2.79/0.76    spl5_50 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 2.79/0.76  fof(f2596,plain,(
% 2.79/0.76    r1_tarski(sK2,sK1) | ~spl5_50),
% 2.79/0.76    inference(superposition,[],[f39,f2569])).
% 2.79/0.76  fof(f2569,plain,(
% 2.79/0.76    sK1 = k2_xboole_0(sK2,sK1) | ~spl5_50),
% 2.79/0.76    inference(avatar_component_clause,[],[f2567])).
% 2.79/0.76  fof(f39,plain,(
% 2.79/0.76    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.79/0.76    inference(cnf_transformation,[],[f12])).
% 2.79/0.76  fof(f12,axiom,(
% 2.79/0.76    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.79/0.76  fof(f2570,plain,(
% 2.79/0.76    spl5_50 | ~spl5_26 | ~spl5_28 | ~spl5_49),
% 2.79/0.76    inference(avatar_split_clause,[],[f2530,f2471,f472,f449,f2567])).
% 2.79/0.76  fof(f2471,plain,(
% 2.79/0.76    spl5_49 <=> sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 2.79/0.76  fof(f2530,plain,(
% 2.79/0.76    sK1 = k2_xboole_0(sK2,sK1) | (~spl5_26 | ~spl5_28 | ~spl5_49)),
% 2.79/0.76    inference(superposition,[],[f2473,f716])).
% 2.79/0.76  fof(f716,plain,(
% 2.79/0.76    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(forward_demodulation,[],[f712,f37])).
% 2.79/0.76  fof(f37,plain,(
% 2.79/0.76    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.79/0.76    inference(cnf_transformation,[],[f11])).
% 2.79/0.76  fof(f11,axiom,(
% 2.79/0.76    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.79/0.76  fof(f712,plain,(
% 2.79/0.76    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X6,k1_xboole_0)) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(superposition,[],[f44,f652])).
% 2.79/0.76  fof(f652,plain,(
% 2.79/0.76    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(superposition,[],[f542,f40])).
% 2.79/0.76  fof(f40,plain,(
% 2.79/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.79/0.76    inference(cnf_transformation,[],[f1])).
% 2.79/0.76  fof(f1,axiom,(
% 2.79/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.79/0.76  fof(f542,plain,(
% 2.79/0.76    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(resolution,[],[f507,f49])).
% 2.79/0.76  fof(f49,plain,(
% 2.79/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.79/0.76    inference(cnf_transformation,[],[f30])).
% 2.79/0.76  fof(f30,plain,(
% 2.79/0.76    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.79/0.76    inference(ennf_transformation,[],[f9])).
% 2.79/0.76  fof(f9,axiom,(
% 2.79/0.76    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.79/0.76  fof(f44,plain,(
% 2.79/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.79/0.76    inference(cnf_transformation,[],[f7])).
% 2.79/0.76  fof(f7,axiom,(
% 2.79/0.76    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.79/0.76  fof(f2473,plain,(
% 2.79/0.76    sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) | ~spl5_49),
% 2.79/0.76    inference(avatar_component_clause,[],[f2471])).
% 2.79/0.76  fof(f2474,plain,(
% 2.79/0.76    spl5_49 | ~spl5_45 | ~spl5_46),
% 2.79/0.76    inference(avatar_split_clause,[],[f2048,f1872,f1831,f2471])).
% 2.79/0.76  fof(f1831,plain,(
% 2.79/0.76    spl5_45 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 2.79/0.76  fof(f1872,plain,(
% 2.79/0.76    spl5_46 <=> sK1 = k5_xboole_0(sK1,sK2)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 2.79/0.76  fof(f2048,plain,(
% 2.79/0.76    sK1 = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) | (~spl5_45 | ~spl5_46)),
% 2.79/0.76    inference(forward_demodulation,[],[f2047,f1874])).
% 2.79/0.76  fof(f1874,plain,(
% 2.79/0.76    sK1 = k5_xboole_0(sK1,sK2) | ~spl5_46),
% 2.79/0.76    inference(avatar_component_clause,[],[f1872])).
% 2.79/0.76  fof(f2047,plain,(
% 2.79/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) | ~spl5_45),
% 2.79/0.76    inference(forward_demodulation,[],[f2032,f41])).
% 2.79/0.76  fof(f41,plain,(
% 2.79/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.79/0.76    inference(cnf_transformation,[],[f2])).
% 2.79/0.76  fof(f2,axiom,(
% 2.79/0.76    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.79/0.76  fof(f2032,plain,(
% 2.79/0.76    k5_xboole_0(sK2,sK1) = k4_xboole_0(k2_xboole_0(sK2,sK1),k1_xboole_0) | ~spl5_45),
% 2.79/0.76    inference(superposition,[],[f45,f1833])).
% 2.79/0.76  fof(f1833,plain,(
% 2.79/0.76    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl5_45),
% 2.79/0.76    inference(avatar_component_clause,[],[f1831])).
% 2.79/0.76  fof(f45,plain,(
% 2.79/0.76    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.79/0.76    inference(cnf_transformation,[],[f6])).
% 2.79/0.76  fof(f6,axiom,(
% 2.79/0.76    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.79/0.76  fof(f1875,plain,(
% 2.79/0.76    spl5_46 | ~spl5_3 | spl5_5 | ~spl5_18 | ~spl5_19 | ~spl5_26 | ~spl5_28 | ~spl5_37),
% 2.79/0.76    inference(avatar_split_clause,[],[f1696,f1353,f472,f449,f268,f263,f90,f81,f1872])).
% 2.79/0.76  fof(f263,plain,(
% 2.79/0.76    spl5_18 <=> k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.79/0.76  fof(f268,plain,(
% 2.79/0.76    spl5_19 <=> sK1 = k2_xboole_0(sK1,sK1)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.79/0.76  fof(f1353,plain,(
% 2.79/0.76    spl5_37 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.79/0.76  fof(f1696,plain,(
% 2.79/0.76    sK1 = k5_xboole_0(sK1,sK2) | (~spl5_3 | spl5_5 | ~spl5_18 | ~spl5_19 | ~spl5_26 | ~spl5_28 | ~spl5_37)),
% 2.79/0.76    inference(subsumption_resolution,[],[f1361,f92])).
% 2.79/0.76  fof(f92,plain,(
% 2.79/0.76    k1_xboole_0 != sK1 | spl5_5),
% 2.79/0.76    inference(avatar_component_clause,[],[f90])).
% 2.79/0.76  fof(f1361,plain,(
% 2.79/0.76    k1_xboole_0 = sK1 | sK1 = k5_xboole_0(sK1,sK2) | (~spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_26 | ~spl5_28 | ~spl5_37)),
% 2.79/0.76    inference(backward_demodulation,[],[f1327,f1355])).
% 2.79/0.76  fof(f1355,plain,(
% 2.79/0.76    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl5_37),
% 2.79/0.76    inference(avatar_component_clause,[],[f1353])).
% 2.79/0.76  fof(f1327,plain,(
% 2.79/0.76    sK1 = k3_xboole_0(sK1,sK2) | sK1 = k5_xboole_0(sK1,sK2) | (~spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(forward_demodulation,[],[f1326,f40])).
% 2.79/0.76  fof(f1326,plain,(
% 2.79/0.76    sK1 = k5_xboole_0(sK1,sK2) | sK1 = k3_xboole_0(sK2,sK1) | (~spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(forward_demodulation,[],[f1297,f716])).
% 2.79/0.76  fof(f1297,plain,(
% 2.79/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | sK1 = k3_xboole_0(sK2,sK1) | (~spl5_3 | ~spl5_18 | ~spl5_19)),
% 2.79/0.76    inference(superposition,[],[f265,f897])).
% 2.79/0.76  fof(f897,plain,(
% 2.79/0.76    ( ! [X9] : (k1_xboole_0 = k3_xboole_0(sK1,X9) | sK1 = k3_xboole_0(X9,sK1)) ) | (~spl5_3 | ~spl5_19)),
% 2.79/0.76    inference(superposition,[],[f40,f631])).
% 2.79/0.76  fof(f631,plain,(
% 2.79/0.76    ( ! [X0] : (sK1 = k3_xboole_0(sK1,X0) | k1_xboole_0 = k3_xboole_0(sK1,X0)) ) | (~spl5_3 | ~spl5_19)),
% 2.79/0.76    inference(resolution,[],[f297,f531])).
% 2.79/0.76  fof(f297,plain,(
% 2.79/0.76    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),sK1)) ) | ~spl5_19),
% 2.79/0.76    inference(superposition,[],[f58,f270])).
% 2.79/0.76  fof(f270,plain,(
% 2.79/0.76    sK1 = k2_xboole_0(sK1,sK1) | ~spl5_19),
% 2.79/0.76    inference(avatar_component_clause,[],[f268])).
% 2.79/0.76  fof(f58,plain,(
% 2.79/0.76    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 2.79/0.76    inference(cnf_transformation,[],[f10])).
% 2.79/0.76  fof(f10,axiom,(
% 2.79/0.76    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).
% 2.79/0.76  fof(f265,plain,(
% 2.79/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl5_18),
% 2.79/0.76    inference(avatar_component_clause,[],[f263])).
% 2.79/0.76  fof(f1834,plain,(
% 2.79/0.76    spl5_45 | ~spl5_3 | spl5_5 | ~spl5_11 | ~spl5_37),
% 2.79/0.76    inference(avatar_split_clause,[],[f1386,f1353,f145,f90,f81,f1831])).
% 2.79/0.76  fof(f145,plain,(
% 2.79/0.76    spl5_11 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.79/0.76  fof(f1386,plain,(
% 2.79/0.76    k1_xboole_0 = k3_xboole_0(sK2,sK1) | (~spl5_3 | spl5_5 | ~spl5_11 | ~spl5_37)),
% 2.79/0.76    inference(subsumption_resolution,[],[f1366,f92])).
% 2.79/0.76  fof(f1366,plain,(
% 2.79/0.76    k1_xboole_0 = sK1 | k1_xboole_0 = k3_xboole_0(sK2,sK1) | (~spl5_3 | ~spl5_11 | ~spl5_37)),
% 2.79/0.76    inference(superposition,[],[f1355,f753])).
% 2.79/0.76  fof(f753,plain,(
% 2.79/0.76    ( ! [X6] : (sK1 = k3_xboole_0(sK1,X6) | k1_xboole_0 = k3_xboole_0(X6,sK1)) ) | (~spl5_3 | ~spl5_11)),
% 2.79/0.76    inference(superposition,[],[f40,f595])).
% 2.79/0.76  fof(f595,plain,(
% 2.79/0.76    ( ! [X0] : (sK1 = k3_xboole_0(X0,sK1) | k1_xboole_0 = k3_xboole_0(X0,sK1)) ) | (~spl5_3 | ~spl5_11)),
% 2.79/0.76    inference(resolution,[],[f531,f252])).
% 2.79/0.76  fof(f252,plain,(
% 2.79/0.76    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,sK1),sK1)) ) | ~spl5_11),
% 2.79/0.76    inference(superposition,[],[f180,f40])).
% 2.79/0.76  fof(f180,plain,(
% 2.79/0.76    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,X0),sK1)) ) | ~spl5_11),
% 2.79/0.76    inference(superposition,[],[f58,f147])).
% 2.79/0.76  fof(f147,plain,(
% 2.79/0.76    sK1 = k2_xboole_0(sK1,sK2) | ~spl5_11),
% 2.79/0.76    inference(avatar_component_clause,[],[f145])).
% 2.79/0.76  fof(f1665,plain,(
% 2.79/0.76    spl5_6 | ~spl5_11 | ~spl5_43),
% 2.79/0.76    inference(avatar_contradiction_clause,[],[f1664])).
% 2.79/0.76  fof(f1664,plain,(
% 2.79/0.76    $false | (spl5_6 | ~spl5_11 | ~spl5_43)),
% 2.79/0.76    inference(subsumption_resolution,[],[f1663,f97])).
% 2.79/0.76  fof(f1663,plain,(
% 2.79/0.76    sK1 = sK2 | (~spl5_11 | ~spl5_43)),
% 2.79/0.76    inference(forward_demodulation,[],[f1662,f147])).
% 2.79/0.76  fof(f1662,plain,(
% 2.79/0.76    sK2 = k2_xboole_0(sK1,sK2) | ~spl5_43),
% 2.79/0.76    inference(resolution,[],[f1636,f48])).
% 2.79/0.76  fof(f1636,plain,(
% 2.79/0.76    r1_tarski(sK1,sK2) | ~spl5_43),
% 2.79/0.76    inference(avatar_component_clause,[],[f1634])).
% 2.79/0.76  fof(f1634,plain,(
% 2.79/0.76    spl5_43 <=> r1_tarski(sK1,sK2)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 2.79/0.76  fof(f1637,plain,(
% 2.79/0.76    spl5_43 | ~spl5_26 | ~spl5_28 | ~spl5_41),
% 2.79/0.76    inference(avatar_split_clause,[],[f1605,f1432,f472,f449,f1634])).
% 2.79/0.76  fof(f1432,plain,(
% 2.79/0.76    spl5_41 <=> sK1 = k3_xboole_0(sK1,sK2)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 2.79/0.76  fof(f1605,plain,(
% 2.79/0.76    r1_tarski(sK1,sK2) | (~spl5_26 | ~spl5_28 | ~spl5_41)),
% 2.79/0.76    inference(superposition,[],[f1163,f1434])).
% 2.79/0.76  fof(f1434,plain,(
% 2.79/0.76    sK1 = k3_xboole_0(sK1,sK2) | ~spl5_41),
% 2.79/0.76    inference(avatar_component_clause,[],[f1432])).
% 2.79/0.76  fof(f1163,plain,(
% 2.79/0.76    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(superposition,[],[f1089,f40])).
% 2.79/0.76  fof(f1089,plain,(
% 2.79/0.76    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X1,X2),X1)) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(superposition,[],[f58,f1026])).
% 2.79/0.76  fof(f1026,plain,(
% 2.79/0.76    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(superposition,[],[f715,f716])).
% 2.79/0.76  fof(f715,plain,(
% 2.79/0.76    ( ! [X5] : (k4_xboole_0(k2_xboole_0(X5,k1_xboole_0),k1_xboole_0) = X5) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(forward_demodulation,[],[f711,f37])).
% 2.79/0.76  fof(f711,plain,(
% 2.79/0.76    ( ! [X5] : (k5_xboole_0(X5,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X5,k1_xboole_0),k1_xboole_0)) ) | (~spl5_26 | ~spl5_28)),
% 2.79/0.76    inference(superposition,[],[f45,f652])).
% 2.79/0.76  fof(f1435,plain,(
% 2.79/0.76    spl5_41 | ~spl5_3 | spl5_5 | ~spl5_18 | ~spl5_19 | ~spl5_26 | ~spl5_28 | ~spl5_38),
% 2.79/0.76    inference(avatar_split_clause,[],[f1410,f1357,f472,f449,f268,f263,f90,f81,f1432])).
% 2.79/0.76  fof(f1357,plain,(
% 2.79/0.76    spl5_38 <=> k1_xboole_0 = k5_xboole_0(sK1,sK2)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.79/0.76  fof(f1410,plain,(
% 2.79/0.76    sK1 = k3_xboole_0(sK1,sK2) | (~spl5_3 | spl5_5 | ~spl5_18 | ~spl5_19 | ~spl5_26 | ~spl5_28 | ~spl5_38)),
% 2.79/0.76    inference(subsumption_resolution,[],[f1407,f92])).
% 2.79/0.76  fof(f1407,plain,(
% 2.79/0.76    k1_xboole_0 = sK1 | sK1 = k3_xboole_0(sK1,sK2) | (~spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_26 | ~spl5_28 | ~spl5_38)),
% 2.79/0.76    inference(backward_demodulation,[],[f1327,f1359])).
% 2.79/0.76  fof(f1359,plain,(
% 2.79/0.76    k1_xboole_0 = k5_xboole_0(sK1,sK2) | ~spl5_38),
% 2.79/0.76    inference(avatar_component_clause,[],[f1357])).
% 2.79/0.76  fof(f1360,plain,(
% 2.79/0.76    spl5_37 | spl5_38 | ~spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_32),
% 2.79/0.76    inference(avatar_split_clause,[],[f911,f617,f268,f263,f81,f1357,f1353])).
% 2.79/0.76  fof(f617,plain,(
% 2.79/0.76    spl5_32 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.79/0.76  fof(f911,plain,(
% 2.79/0.76    k1_xboole_0 = k5_xboole_0(sK1,sK2) | k1_xboole_0 = k3_xboole_0(sK1,sK2) | (~spl5_3 | ~spl5_18 | ~spl5_19 | ~spl5_32)),
% 2.79/0.76    inference(forward_demodulation,[],[f894,f619])).
% 2.79/0.76  fof(f619,plain,(
% 2.79/0.76    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl5_32),
% 2.79/0.76    inference(avatar_component_clause,[],[f617])).
% 2.79/0.76  fof(f894,plain,(
% 2.79/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | k1_xboole_0 = k3_xboole_0(sK1,sK2) | (~spl5_3 | ~spl5_18 | ~spl5_19)),
% 2.79/0.76    inference(superposition,[],[f265,f631])).
% 2.79/0.76  fof(f620,plain,(
% 2.79/0.76    spl5_32 | ~spl5_17 | ~spl5_19),
% 2.79/0.76    inference(avatar_split_clause,[],[f295,f268,f258,f617])).
% 2.79/0.76  fof(f258,plain,(
% 2.79/0.76    spl5_17 <=> sK1 = k3_xboole_0(sK1,sK1)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.79/0.76  fof(f295,plain,(
% 2.79/0.76    k1_xboole_0 = k4_xboole_0(sK1,sK1) | (~spl5_17 | ~spl5_19)),
% 2.79/0.76    inference(forward_demodulation,[],[f294,f36])).
% 2.79/0.76  fof(f36,plain,(
% 2.79/0.76    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.79/0.76    inference(cnf_transformation,[],[f14])).
% 2.79/0.76  fof(f14,axiom,(
% 2.79/0.76    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.79/0.76  fof(f294,plain,(
% 2.79/0.76    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK1) | (~spl5_17 | ~spl5_19)),
% 2.79/0.76    inference(forward_demodulation,[],[f292,f270])).
% 2.79/0.76  fof(f292,plain,(
% 2.79/0.76    k5_xboole_0(sK1,sK1) = k4_xboole_0(k2_xboole_0(sK1,sK1),sK1) | ~spl5_17),
% 2.79/0.76    inference(superposition,[],[f45,f260])).
% 2.79/0.76  fof(f260,plain,(
% 2.79/0.76    sK1 = k3_xboole_0(sK1,sK1) | ~spl5_17),
% 2.79/0.76    inference(avatar_component_clause,[],[f258])).
% 2.79/0.76  fof(f475,plain,(
% 2.79/0.76    spl5_28 | ~spl5_26),
% 2.79/0.76    inference(avatar_split_clause,[],[f463,f449,f472])).
% 2.79/0.76  fof(f463,plain,(
% 2.79/0.76    r1_xboole_0(k1_xboole_0,k1_tarski(sK0)) | ~spl5_26),
% 2.79/0.76    inference(trivial_inequality_removal,[],[f460])).
% 2.79/0.76  fof(f460,plain,(
% 2.79/0.76    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_tarski(sK0)) | ~spl5_26),
% 2.79/0.76    inference(superposition,[],[f50,f451])).
% 2.79/0.76  fof(f50,plain,(
% 2.79/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.79/0.76    inference(cnf_transformation,[],[f4])).
% 2.79/0.76  fof(f4,axiom,(
% 2.79/0.76    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.79/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.79/0.76  fof(f452,plain,(
% 2.79/0.76    spl5_26 | ~spl5_5 | ~spl5_7),
% 2.79/0.76    inference(avatar_split_clause,[],[f382,f100,f90,f449])).
% 2.79/0.76  fof(f100,plain,(
% 2.79/0.76    spl5_7 <=> r1_tarski(sK1,k1_tarski(sK0))),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.79/0.76  fof(f382,plain,(
% 2.79/0.76    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) | (~spl5_5 | ~spl5_7)),
% 2.79/0.76    inference(backward_demodulation,[],[f105,f91])).
% 2.79/0.76  fof(f105,plain,(
% 2.79/0.76    sK1 = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl5_7),
% 2.79/0.76    inference(resolution,[],[f102,f49])).
% 2.79/0.76  fof(f102,plain,(
% 2.79/0.76    r1_tarski(sK1,k1_tarski(sK0)) | ~spl5_7),
% 2.79/0.76    inference(avatar_component_clause,[],[f100])).
% 2.79/0.76  fof(f277,plain,(
% 2.79/0.76    spl5_20 | ~spl5_13),
% 2.79/0.76    inference(avatar_split_clause,[],[f226,f184,f274])).
% 2.79/0.76  fof(f274,plain,(
% 2.79/0.76    spl5_20 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.79/0.76  fof(f184,plain,(
% 2.79/0.76    spl5_13 <=> r1_tarski(k1_xboole_0,sK1)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.79/0.76  fof(f226,plain,(
% 2.79/0.76    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) | ~spl5_13),
% 2.79/0.76    inference(resolution,[],[f186,f49])).
% 2.79/0.76  fof(f186,plain,(
% 2.79/0.76    r1_tarski(k1_xboole_0,sK1) | ~spl5_13),
% 2.79/0.76    inference(avatar_component_clause,[],[f184])).
% 2.79/0.76  fof(f271,plain,(
% 2.79/0.76    spl5_19 | ~spl5_10),
% 2.79/0.76    inference(avatar_split_clause,[],[f175,f135,f268])).
% 2.79/0.76  fof(f135,plain,(
% 2.79/0.76    spl5_10 <=> r1_tarski(sK1,sK1)),
% 2.79/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.79/0.76  fof(f175,plain,(
% 2.79/0.76    sK1 = k2_xboole_0(sK1,sK1) | ~spl5_10),
% 2.79/0.76    inference(resolution,[],[f137,f48])).
% 2.79/0.76  fof(f137,plain,(
% 2.79/0.76    r1_tarski(sK1,sK1) | ~spl5_10),
% 2.79/0.76    inference(avatar_component_clause,[],[f135])).
% 2.79/0.76  fof(f266,plain,(
% 2.79/0.76    spl5_18 | ~spl5_1 | ~spl5_3),
% 2.79/0.76    inference(avatar_split_clause,[],[f241,f81,f69,f263])).
% 2.79/0.76  fof(f241,plain,(
% 2.79/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | (~spl5_1 | ~spl5_3)),
% 2.79/0.76    inference(forward_demodulation,[],[f75,f82])).
% 2.79/0.76  fof(f75,plain,(
% 2.79/0.76    k5_xboole_0(sK1,sK2) = k4_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,sK2)) | ~spl5_1),
% 2.79/0.76    inference(superposition,[],[f45,f71])).
% 2.79/0.76  fof(f261,plain,(
% 2.79/0.76    spl5_17 | ~spl5_10),
% 2.79/0.76    inference(avatar_split_clause,[],[f174,f135,f258])).
% 2.79/0.76  fof(f174,plain,(
% 2.79/0.76    sK1 = k3_xboole_0(sK1,sK1) | ~spl5_10),
% 2.79/0.76    inference(resolution,[],[f137,f49])).
% 2.79/0.76  fof(f245,plain,(
% 2.79/0.76    spl5_11 | ~spl5_1 | ~spl5_3),
% 2.79/0.76    inference(avatar_split_clause,[],[f127,f81,f69,f145])).
% 2.79/0.76  fof(f127,plain,(
% 2.79/0.76    sK1 = k2_xboole_0(sK1,sK2) | (~spl5_1 | ~spl5_3)),
% 2.79/0.76    inference(backward_demodulation,[],[f71,f82])).
% 2.79/0.76  fof(f187,plain,(
% 2.79/0.76    spl5_13 | ~spl5_3),
% 2.79/0.76    inference(avatar_split_clause,[],[f141,f81,f184])).
% 2.79/0.76  fof(f141,plain,(
% 2.79/0.76    r1_tarski(k1_xboole_0,sK1) | ~spl5_3),
% 2.79/0.76    inference(superposition,[],[f66,f82])).
% 2.79/0.76  fof(f66,plain,(
% 2.79/0.76    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 2.79/0.76    inference(equality_resolution,[],[f56])).
% 2.79/0.76  fof(f56,plain,(
% 2.79/0.76    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 2.79/0.76    inference(cnf_transformation,[],[f22])).
% 2.79/0.76  fof(f138,plain,(
% 2.79/0.76    spl5_10 | ~spl5_3 | ~spl5_7),
% 2.79/0.76    inference(avatar_split_clause,[],[f131,f100,f81,f135])).
% 2.79/0.76  fof(f131,plain,(
% 2.79/0.76    r1_tarski(sK1,sK1) | (~spl5_3 | ~spl5_7)),
% 2.79/0.76    inference(backward_demodulation,[],[f102,f82])).
% 2.79/0.76  fof(f115,plain,(
% 2.79/0.76    spl5_5 | spl5_3 | ~spl5_7),
% 2.79/0.76    inference(avatar_split_clause,[],[f107,f100,f81,f90])).
% 2.79/0.76  fof(f107,plain,(
% 2.79/0.76    k1_xboole_0 = sK1 | (spl5_3 | ~spl5_7)),
% 2.79/0.76    inference(subsumption_resolution,[],[f104,f83])).
% 2.79/0.76  fof(f83,plain,(
% 2.79/0.76    sK1 != k1_tarski(sK0) | spl5_3),
% 2.79/0.76    inference(avatar_component_clause,[],[f81])).
% 2.79/0.76  fof(f104,plain,(
% 2.79/0.76    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1 | ~spl5_7),
% 2.79/0.76    inference(resolution,[],[f102,f55])).
% 2.79/0.76  fof(f103,plain,(
% 2.79/0.76    spl5_7 | ~spl5_1),
% 2.79/0.76    inference(avatar_split_clause,[],[f74,f69,f100])).
% 2.79/0.76  fof(f74,plain,(
% 2.79/0.76    r1_tarski(sK1,k1_tarski(sK0)) | ~spl5_1),
% 2.79/0.76    inference(superposition,[],[f39,f71])).
% 2.79/0.76  fof(f98,plain,(
% 2.79/0.76    ~spl5_6 | ~spl5_3),
% 2.79/0.76    inference(avatar_split_clause,[],[f67,f81,f95])).
% 2.79/0.76  fof(f67,plain,(
% 2.79/0.76    sK1 != k1_tarski(sK0) | sK1 != sK2),
% 2.79/0.76    inference(inner_rewriting,[],[f34])).
% 2.79/0.76  fof(f34,plain,(
% 2.79/0.76    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 2.79/0.76    inference(cnf_transformation,[],[f27])).
% 2.79/0.76  fof(f84,plain,(
% 2.79/0.76    ~spl5_2 | ~spl5_3),
% 2.79/0.76    inference(avatar_split_clause,[],[f32,f81,f77])).
% 2.79/0.76  fof(f32,plain,(
% 2.79/0.76    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.79/0.76    inference(cnf_transformation,[],[f27])).
% 2.79/0.76  fof(f72,plain,(
% 2.79/0.76    spl5_1),
% 2.79/0.76    inference(avatar_split_clause,[],[f35,f69])).
% 2.79/0.76  fof(f35,plain,(
% 2.79/0.76    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.79/0.76    inference(cnf_transformation,[],[f27])).
% 2.79/0.76  % SZS output end Proof for theBenchmark
% 2.79/0.76  % (13202)------------------------------
% 2.79/0.76  % (13202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.79/0.76  % (13202)Termination reason: Refutation
% 2.79/0.76  
% 2.79/0.76  % (13202)Memory used [KB]: 12537
% 2.79/0.76  % (13202)Time elapsed: 0.297 s
% 2.79/0.76  % (13202)------------------------------
% 2.79/0.76  % (13202)------------------------------
% 3.01/0.77  % (13181)Success in time 0.398 s
%------------------------------------------------------------------------------
