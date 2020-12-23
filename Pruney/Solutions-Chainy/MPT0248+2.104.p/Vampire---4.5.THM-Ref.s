%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:05 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 317 expanded)
%              Number of leaves         :   41 ( 130 expanded)
%              Depth                    :   10
%              Number of atoms          :  406 ( 756 expanded)
%              Number of equality atoms :  131 ( 329 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1026,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f123,f132,f141,f170,f183,f195,f233,f260,f276,f299,f357,f369,f444,f463,f474,f478,f488,f911,f924,f935,f1008,f1015,f1025])).

fof(f1025,plain,
    ( ~ spl6_11
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f1020,f138,f252])).

fof(f252,plain,
    ( spl6_11
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f138,plain,
    ( spl6_5
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1020,plain,
    ( sK1 != sK2
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f1019,f139])).

fof(f139,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f1019,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_5 ),
    inference(trivial_inequality_removal,[],[f1018])).

fof(f1018,plain,
    ( sK1 != sK1
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f89,f139])).

fof(f89,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f44,f87,f87])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f1015,plain,
    ( spl6_4
    | ~ spl6_5
    | spl6_11
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f1010])).

fof(f1010,plain,
    ( $false
    | spl6_4
    | ~ spl6_5
    | spl6_11
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f136,f254,f1007,f514])).

fof(f514,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,sK1)
        | sK1 = X10
        | k1_xboole_0 = X10 )
    | ~ spl6_5 ),
    inference(duplicate_literal_removal,[],[f505])).

fof(f505,plain,
    ( ! [X10] :
        ( ~ r1_tarski(X10,sK1)
        | sK1 = X10
        | sK1 = X10
        | sK1 = X10
        | k1_xboole_0 = X10 )
    | ~ spl6_5 ),
    inference(superposition,[],[f107,f139])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f81,f87,f87,f57,f57])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f1007,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f1005])).

fof(f1005,plain,
    ( spl6_34
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f254,plain,
    ( sK1 != sK2
    | spl6_11 ),
    inference(avatar_component_clause,[],[f252])).

fof(f136,plain,
    ( k1_xboole_0 != sK2
    | spl6_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f1008,plain,
    ( ~ spl6_33
    | spl6_34
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f938,f273,f230,f1005,f908])).

fof(f908,plain,
    ( spl6_33
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f230,plain,
    ( spl6_10
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f273,plain,
    ( spl6_14
  <=> sK2 = k2_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f938,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(superposition,[],[f549,f274])).

fof(f274,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f273])).

fof(f549,plain,
    ( ! [X5] :
        ( r1_tarski(k2_xboole_0(X5,sK2),sK1)
        | ~ r1_tarski(X5,sK1) )
    | ~ spl6_10 ),
    inference(superposition,[],[f73,f232])).

fof(f232,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f230])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f935,plain,
    ( spl6_14
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f934])).

fof(f934,plain,
    ( $false
    | spl6_14
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f906,f46,f49,f275,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)
      | ~ r1_xboole_0(X2,X0)
      | ~ r1_xboole_0(X3,X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f275,plain,
    ( sK2 != k2_xboole_0(k1_xboole_0,sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f273])).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f906,plain,
    ( ! [X1] : r1_xboole_0(k1_xboole_0,X1)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f905])).

fof(f905,plain,
    ( spl6_32
  <=> ! [X1] : r1_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f924,plain,(
    spl6_33 ),
    inference(avatar_contradiction_clause,[],[f916])).

fof(f916,plain,
    ( $false
    | spl6_33 ),
    inference(unit_resulting_resolution,[],[f48,f910,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f910,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl6_33 ),
    inference(avatar_component_clause,[],[f908])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f911,plain,
    ( spl6_32
    | ~ spl6_33
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f902,f257,f908,f905])).

fof(f257,plain,
    ( spl6_12
  <=> r1_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f902,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,sK1)
        | r1_xboole_0(k1_xboole_0,X1) )
    | ~ spl6_12 ),
    inference(duplicate_literal_removal,[],[f900])).

fof(f900,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,sK1)
        | r1_xboole_0(k1_xboole_0,X1)
        | r1_xboole_0(k1_xboole_0,X1) )
    | ~ spl6_12 ),
    inference(resolution,[],[f757,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f757,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(sK4(k1_xboole_0,X5),X6)
        | ~ r1_tarski(X6,sK1)
        | r1_xboole_0(k1_xboole_0,X5) )
    | ~ spl6_12 ),
    inference(resolution,[],[f552,f61])).

fof(f552,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,sK1) )
    | ~ spl6_12 ),
    inference(resolution,[],[f516,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f516,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f259,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f259,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f257])).

fof(f488,plain,
    ( ~ spl6_3
    | spl6_14
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | ~ spl6_3
    | spl6_14
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f275,f46,f49,f483,f86])).

fof(f483,plain,
    ( ! [X3] : r1_xboole_0(k1_xboole_0,X3)
    | ~ spl6_3
    | ~ spl6_22 ),
    inference(resolution,[],[f479,f61])).

fof(f479,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f443,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f443,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f442])).

fof(f442,plain,
    ( spl6_22
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f478,plain,(
    spl6_24 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | spl6_24 ),
    inference(unit_resulting_resolution,[],[f46,f473])).

fof(f473,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl6_24
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f474,plain,
    ( ~ spl6_24
    | ~ spl6_3
    | spl6_21 ),
    inference(avatar_split_clause,[],[f468,f438,f129,f471])).

fof(f438,plain,
    ( spl6_21
  <=> r1_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f468,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | spl6_21 ),
    inference(backward_demodulation,[],[f440,f130])).

fof(f440,plain,
    ( ~ r1_xboole_0(sK1,sK1)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f438])).

fof(f463,plain,
    ( k1_xboole_0 != sK1
    | sK1 != k4_xboole_0(sK1,sK1)
    | k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f444,plain,
    ( ~ spl6_21
    | spl6_22
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f397,f331,f442,f438])).

fof(f331,plain,
    ( spl6_17
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r1_xboole_0(sK1,sK1) )
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f393,f50])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f393,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k4_xboole_0(sK1,k1_xboole_0))
        | ~ r1_xboole_0(sK1,sK1) )
    | ~ spl6_17 ),
    inference(superposition,[],[f95,f333])).

fof(f333,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f331])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f369,plain,(
    spl6_18 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f47,f356,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f356,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl6_18
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f357,plain,
    ( ~ spl6_18
    | ~ spl6_3
    | spl6_16 ),
    inference(avatar_split_clause,[],[f349,f326,f129,f354])).

fof(f326,plain,
    ( spl6_16
  <=> sK1 = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f349,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | spl6_16 ),
    inference(forward_demodulation,[],[f328,f130])).

fof(f328,plain,
    ( sK1 != k4_xboole_0(sK1,sK1)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f326])).

fof(f299,plain,
    ( spl6_5
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f297,f230,f120,f138])).

fof(f120,plain,
    ( spl6_1
  <=> k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f297,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_1
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f122,f232])).

fof(f122,plain,
    ( k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f276,plain,
    ( ~ spl6_14
    | ~ spl6_3
    | spl6_6 ),
    inference(avatar_split_clause,[],[f263,f167,f129,f273])).

fof(f167,plain,
    ( spl6_6
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f263,plain,
    ( sK2 != k2_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_3
    | spl6_6 ),
    inference(forward_demodulation,[],[f169,f130])).

fof(f169,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f260,plain,
    ( spl6_12
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f241,f230,f192,f257])).

fof(f192,plain,
    ( spl6_8
  <=> r1_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f241,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f194,f232])).

fof(f194,plain,
    ( r1_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f192])).

fof(f233,plain,
    ( spl6_3
    | spl6_10
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f222,f120,f230,f129])).

fof(f222,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ spl6_1 ),
    inference(resolution,[],[f164,f53])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f164,plain,
    ( ! [X9] :
        ( ~ r1_tarski(X9,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = X9
        | k1_xboole_0 = X9 )
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,
    ( ! [X9] :
        ( ~ r1_tarski(X9,k2_xboole_0(sK1,sK2))
        | k2_xboole_0(sK1,sK2) = X9
        | k2_xboole_0(sK1,sK2) = X9
        | k2_xboole_0(sK1,sK2) = X9
        | k1_xboole_0 = X9 )
    | ~ spl6_1 ),
    inference(superposition,[],[f107,f122])).

fof(f195,plain,
    ( spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f187,f180,f192])).

fof(f180,plain,
    ( spl6_7
  <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f187,plain,
    ( r1_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))
    | ~ spl6_7 ),
    inference(superposition,[],[f52,f182])).

fof(f182,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f180])).

fof(f52,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f183,plain,
    ( spl6_7
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f153,f120,f180])).

fof(f153,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))
    | ~ spl6_1 ),
    inference(superposition,[],[f93,f122])).

fof(f93,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f87,f57])).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f170,plain,
    ( ~ spl6_6
    | ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f142,f125,f120,f167])).

fof(f125,plain,
    ( spl6_2
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f142,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | ~ spl6_1
    | spl6_2 ),
    inference(superposition,[],[f127,f122])).

fof(f127,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f125])).

fof(f141,plain,
    ( ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f91,f138,f134])).

fof(f91,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f42,f87])).

fof(f42,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f132,plain,
    ( ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f90,f129,f125])).

fof(f90,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f43,f87])).

fof(f43,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f123,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f88,f120])).

fof(f88,plain,(
    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f45,f87])).

fof(f45,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:23:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.52  % (20750)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (20733)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (20758)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (20730)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (20742)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (20747)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (20732)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (20729)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (20746)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (20751)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (20728)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (20727)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (20743)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (20739)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (20740)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (20741)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (20749)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (20735)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (20731)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (20745)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (20734)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (20753)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (20748)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (20737)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (20757)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (20756)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (20752)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (20738)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.56  % (20750)Refutation found. Thanks to Tanya!
% 1.45/0.56  % SZS status Theorem for theBenchmark
% 1.45/0.57  % (20755)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.57  % (20744)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.58/0.58  % SZS output start Proof for theBenchmark
% 1.58/0.58  fof(f1026,plain,(
% 1.58/0.58    $false),
% 1.58/0.58    inference(avatar_sat_refutation,[],[f123,f132,f141,f170,f183,f195,f233,f260,f276,f299,f357,f369,f444,f463,f474,f478,f488,f911,f924,f935,f1008,f1015,f1025])).
% 1.58/0.58  fof(f1025,plain,(
% 1.58/0.58    ~spl6_11 | ~spl6_5),
% 1.58/0.58    inference(avatar_split_clause,[],[f1020,f138,f252])).
% 1.58/0.58  fof(f252,plain,(
% 1.58/0.58    spl6_11 <=> sK1 = sK2),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.58/0.58  fof(f138,plain,(
% 1.58/0.58    spl6_5 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.58/0.58  fof(f1020,plain,(
% 1.58/0.58    sK1 != sK2 | ~spl6_5),
% 1.58/0.58    inference(forward_demodulation,[],[f1019,f139])).
% 1.58/0.58  fof(f139,plain,(
% 1.58/0.58    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_5),
% 1.58/0.58    inference(avatar_component_clause,[],[f138])).
% 1.58/0.58  fof(f1019,plain,(
% 1.58/0.58    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_5),
% 1.58/0.58    inference(trivial_inequality_removal,[],[f1018])).
% 1.58/0.58  fof(f1018,plain,(
% 1.58/0.58    sK1 != sK1 | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_5),
% 1.58/0.58    inference(forward_demodulation,[],[f89,f139])).
% 1.58/0.58  fof(f89,plain,(
% 1.58/0.58    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.58/0.58    inference(definition_unfolding,[],[f44,f87,f87])).
% 1.58/0.58  fof(f87,plain,(
% 1.58/0.58    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.58/0.58    inference(definition_unfolding,[],[f51,f57])).
% 1.58/0.58  fof(f57,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f19])).
% 1.58/0.58  fof(f19,axiom,(
% 1.58/0.58    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.58/0.58  fof(f51,plain,(
% 1.58/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f18])).
% 1.58/0.58  fof(f18,axiom,(
% 1.58/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.58/0.58  fof(f44,plain,(
% 1.58/0.58    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f29])).
% 1.58/0.58  fof(f29,plain,(
% 1.58/0.58    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.58/0.58    inference(ennf_transformation,[],[f26])).
% 1.58/0.58  fof(f26,negated_conjecture,(
% 1.58/0.58    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.58/0.58    inference(negated_conjecture,[],[f25])).
% 1.58/0.58  fof(f25,conjecture,(
% 1.58/0.58    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.58/0.58  fof(f1015,plain,(
% 1.58/0.58    spl6_4 | ~spl6_5 | spl6_11 | ~spl6_34),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f1010])).
% 1.58/0.58  fof(f1010,plain,(
% 1.58/0.58    $false | (spl6_4 | ~spl6_5 | spl6_11 | ~spl6_34)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f136,f254,f1007,f514])).
% 1.58/0.58  fof(f514,plain,(
% 1.58/0.58    ( ! [X10] : (~r1_tarski(X10,sK1) | sK1 = X10 | k1_xboole_0 = X10) ) | ~spl6_5),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f505])).
% 1.58/0.58  fof(f505,plain,(
% 1.58/0.58    ( ! [X10] : (~r1_tarski(X10,sK1) | sK1 = X10 | sK1 = X10 | sK1 = X10 | k1_xboole_0 = X10) ) | ~spl6_5),
% 1.58/0.58    inference(superposition,[],[f107,f139])).
% 1.58/0.58  fof(f107,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 1.58/0.58    inference(definition_unfolding,[],[f81,f87,f87,f57,f57])).
% 1.58/0.58  fof(f81,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.58/0.58    inference(cnf_transformation,[],[f39])).
% 1.58/0.58  fof(f39,plain,(
% 1.58/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.58/0.58    inference(ennf_transformation,[],[f20])).
% 1.58/0.58  fof(f20,axiom,(
% 1.58/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.58/0.58  fof(f1007,plain,(
% 1.58/0.58    r1_tarski(sK2,sK1) | ~spl6_34),
% 1.58/0.58    inference(avatar_component_clause,[],[f1005])).
% 1.58/0.58  fof(f1005,plain,(
% 1.58/0.58    spl6_34 <=> r1_tarski(sK2,sK1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.58/0.58  fof(f254,plain,(
% 1.58/0.58    sK1 != sK2 | spl6_11),
% 1.58/0.58    inference(avatar_component_clause,[],[f252])).
% 1.58/0.58  fof(f136,plain,(
% 1.58/0.58    k1_xboole_0 != sK2 | spl6_4),
% 1.58/0.58    inference(avatar_component_clause,[],[f134])).
% 1.58/0.58  fof(f134,plain,(
% 1.58/0.58    spl6_4 <=> k1_xboole_0 = sK2),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.58/0.58  fof(f1008,plain,(
% 1.58/0.58    ~spl6_33 | spl6_34 | ~spl6_10 | ~spl6_14),
% 1.58/0.58    inference(avatar_split_clause,[],[f938,f273,f230,f1005,f908])).
% 1.58/0.58  fof(f908,plain,(
% 1.58/0.58    spl6_33 <=> r1_tarski(k1_xboole_0,sK1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.58/0.58  fof(f230,plain,(
% 1.58/0.58    spl6_10 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.58/0.58  fof(f273,plain,(
% 1.58/0.58    spl6_14 <=> sK2 = k2_xboole_0(k1_xboole_0,sK2)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.58/0.58  fof(f938,plain,(
% 1.58/0.58    r1_tarski(sK2,sK1) | ~r1_tarski(k1_xboole_0,sK1) | (~spl6_10 | ~spl6_14)),
% 1.58/0.58    inference(superposition,[],[f549,f274])).
% 1.58/0.58  fof(f274,plain,(
% 1.58/0.58    sK2 = k2_xboole_0(k1_xboole_0,sK2) | ~spl6_14),
% 1.58/0.58    inference(avatar_component_clause,[],[f273])).
% 1.58/0.58  fof(f549,plain,(
% 1.58/0.58    ( ! [X5] : (r1_tarski(k2_xboole_0(X5,sK2),sK1) | ~r1_tarski(X5,sK1)) ) | ~spl6_10),
% 1.58/0.58    inference(superposition,[],[f73,f232])).
% 1.58/0.58  fof(f232,plain,(
% 1.58/0.58    sK1 = k2_xboole_0(sK1,sK2) | ~spl6_10),
% 1.58/0.58    inference(avatar_component_clause,[],[f230])).
% 1.58/0.58  fof(f73,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f33])).
% 1.58/0.58  fof(f33,plain,(
% 1.58/0.58    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 1.58/0.58    inference(ennf_transformation,[],[f17])).
% 1.58/0.58  fof(f17,axiom,(
% 1.58/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 1.58/0.58  fof(f935,plain,(
% 1.58/0.58    spl6_14 | ~spl6_32),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f934])).
% 1.58/0.58  fof(f934,plain,(
% 1.58/0.58    $false | (spl6_14 | ~spl6_32)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f906,f46,f49,f275,f86])).
% 1.58/0.58  fof(f86,plain,(
% 1.58/0.58    ( ! [X2,X0,X3,X1] : (k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) | ~r1_xboole_0(X2,X0) | ~r1_xboole_0(X3,X1) | X1 = X2) )),
% 1.58/0.58    inference(cnf_transformation,[],[f41])).
% 1.58/0.58  fof(f41,plain,(
% 1.58/0.58    ! [X0,X1,X2,X3] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3))),
% 1.58/0.58    inference(flattening,[],[f40])).
% 1.58/0.58  fof(f40,plain,(
% 1.58/0.58    ! [X0,X1,X2,X3] : (X1 = X2 | (~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)))),
% 1.58/0.58    inference(ennf_transformation,[],[f13])).
% 1.58/0.58  fof(f13,axiom,(
% 1.58/0.58    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.58/0.58  fof(f275,plain,(
% 1.58/0.58    sK2 != k2_xboole_0(k1_xboole_0,sK2) | spl6_14),
% 1.58/0.58    inference(avatar_component_clause,[],[f273])).
% 1.58/0.58  fof(f49,plain,(
% 1.58/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.58/0.58    inference(cnf_transformation,[],[f5])).
% 1.58/0.58  fof(f5,axiom,(
% 1.58/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.58/0.58  fof(f46,plain,(
% 1.58/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f12])).
% 1.58/0.58  fof(f12,axiom,(
% 1.58/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.58/0.58  fof(f906,plain,(
% 1.58/0.58    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) ) | ~spl6_32),
% 1.58/0.58    inference(avatar_component_clause,[],[f905])).
% 1.58/0.58  fof(f905,plain,(
% 1.58/0.58    spl6_32 <=> ! [X1] : r1_xboole_0(k1_xboole_0,X1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.58/0.58  fof(f924,plain,(
% 1.58/0.58    spl6_33),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f916])).
% 1.58/0.58  fof(f916,plain,(
% 1.58/0.58    $false | spl6_33),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f48,f910,f70])).
% 1.58/0.58  fof(f70,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f8])).
% 1.58/0.58  fof(f8,axiom,(
% 1.58/0.58    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.58/0.58  fof(f910,plain,(
% 1.58/0.58    ~r1_tarski(k1_xboole_0,sK1) | spl6_33),
% 1.58/0.58    inference(avatar_component_clause,[],[f908])).
% 1.58/0.58  fof(f48,plain,(
% 1.58/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f11])).
% 1.58/0.58  fof(f11,axiom,(
% 1.58/0.58    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.58/0.58  fof(f911,plain,(
% 1.58/0.58    spl6_32 | ~spl6_33 | ~spl6_12),
% 1.58/0.58    inference(avatar_split_clause,[],[f902,f257,f908,f905])).
% 1.58/0.58  fof(f257,plain,(
% 1.58/0.58    spl6_12 <=> r1_xboole_0(k1_xboole_0,sK1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.58/0.58  fof(f902,plain,(
% 1.58/0.58    ( ! [X1] : (~r1_tarski(k1_xboole_0,sK1) | r1_xboole_0(k1_xboole_0,X1)) ) | ~spl6_12),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f900])).
% 1.58/0.58  fof(f900,plain,(
% 1.58/0.58    ( ! [X1] : (~r1_tarski(k1_xboole_0,sK1) | r1_xboole_0(k1_xboole_0,X1) | r1_xboole_0(k1_xboole_0,X1)) ) | ~spl6_12),
% 1.58/0.58    inference(resolution,[],[f757,f61])).
% 1.58/0.58  fof(f61,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f31])).
% 1.58/0.58  fof(f31,plain,(
% 1.58/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.58/0.58    inference(ennf_transformation,[],[f28])).
% 1.58/0.58  fof(f28,plain,(
% 1.58/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.58/0.58    inference(rectify,[],[f2])).
% 1.58/0.58  fof(f2,axiom,(
% 1.58/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.58/0.58  fof(f757,plain,(
% 1.58/0.58    ( ! [X6,X5] : (~r2_hidden(sK4(k1_xboole_0,X5),X6) | ~r1_tarski(X6,sK1) | r1_xboole_0(k1_xboole_0,X5)) ) | ~spl6_12),
% 1.58/0.58    inference(resolution,[],[f552,f61])).
% 1.58/0.58  fof(f552,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1) | ~r1_tarski(X1,sK1)) ) | ~spl6_12),
% 1.58/0.58    inference(resolution,[],[f516,f66])).
% 1.58/0.58  fof(f66,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f32])).
% 1.58/0.58  fof(f32,plain,(
% 1.58/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f1])).
% 1.58/0.58  fof(f1,axiom,(
% 1.58/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.58/0.58  fof(f516,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_12),
% 1.58/0.58    inference(resolution,[],[f259,f60])).
% 1.58/0.58  fof(f60,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f31])).
% 1.58/0.58  fof(f259,plain,(
% 1.58/0.58    r1_xboole_0(k1_xboole_0,sK1) | ~spl6_12),
% 1.58/0.58    inference(avatar_component_clause,[],[f257])).
% 1.58/0.58  fof(f488,plain,(
% 1.58/0.58    ~spl6_3 | spl6_14 | ~spl6_22),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f485])).
% 1.58/0.58  fof(f485,plain,(
% 1.58/0.58    $false | (~spl6_3 | spl6_14 | ~spl6_22)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f275,f46,f49,f483,f86])).
% 1.58/0.58  fof(f483,plain,(
% 1.58/0.58    ( ! [X3] : (r1_xboole_0(k1_xboole_0,X3)) ) | (~spl6_3 | ~spl6_22)),
% 1.58/0.58    inference(resolution,[],[f479,f61])).
% 1.58/0.58  fof(f479,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_3 | ~spl6_22)),
% 1.58/0.58    inference(forward_demodulation,[],[f443,f130])).
% 1.58/0.58  fof(f130,plain,(
% 1.58/0.58    k1_xboole_0 = sK1 | ~spl6_3),
% 1.58/0.58    inference(avatar_component_clause,[],[f129])).
% 1.58/0.58  fof(f129,plain,(
% 1.58/0.58    spl6_3 <=> k1_xboole_0 = sK1),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.58/0.58  fof(f443,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl6_22),
% 1.58/0.58    inference(avatar_component_clause,[],[f442])).
% 1.58/0.58  fof(f442,plain,(
% 1.58/0.58    spl6_22 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.58/0.58  fof(f478,plain,(
% 1.58/0.58    spl6_24),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f475])).
% 1.58/0.58  fof(f475,plain,(
% 1.58/0.58    $false | spl6_24),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f46,f473])).
% 1.58/0.58  fof(f473,plain,(
% 1.58/0.58    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl6_24),
% 1.58/0.58    inference(avatar_component_clause,[],[f471])).
% 1.58/0.58  fof(f471,plain,(
% 1.58/0.58    spl6_24 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.58/0.58  fof(f474,plain,(
% 1.58/0.58    ~spl6_24 | ~spl6_3 | spl6_21),
% 1.58/0.58    inference(avatar_split_clause,[],[f468,f438,f129,f471])).
% 1.58/0.58  fof(f438,plain,(
% 1.58/0.58    spl6_21 <=> r1_xboole_0(sK1,sK1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.58/0.58  fof(f468,plain,(
% 1.58/0.58    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl6_3 | spl6_21)),
% 1.58/0.58    inference(backward_demodulation,[],[f440,f130])).
% 1.58/0.58  fof(f440,plain,(
% 1.58/0.58    ~r1_xboole_0(sK1,sK1) | spl6_21),
% 1.58/0.58    inference(avatar_component_clause,[],[f438])).
% 1.58/0.58  fof(f463,plain,(
% 1.58/0.58    k1_xboole_0 != sK1 | sK1 != k4_xboole_0(sK1,sK1) | k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.58/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.58/0.58  fof(f444,plain,(
% 1.58/0.58    ~spl6_21 | spl6_22 | ~spl6_17),
% 1.58/0.58    inference(avatar_split_clause,[],[f397,f331,f442,f438])).
% 1.58/0.58  fof(f331,plain,(
% 1.58/0.58    spl6_17 <=> k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 1.58/0.58  fof(f397,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r1_xboole_0(sK1,sK1)) ) | ~spl6_17),
% 1.58/0.58    inference(forward_demodulation,[],[f393,f50])).
% 1.58/0.58  fof(f50,plain,(
% 1.58/0.58    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.58/0.58    inference(cnf_transformation,[],[f9])).
% 1.58/0.58  fof(f9,axiom,(
% 1.58/0.58    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.58/0.58  fof(f393,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,k1_xboole_0)) | ~r1_xboole_0(sK1,sK1)) ) | ~spl6_17),
% 1.58/0.58    inference(superposition,[],[f95,f333])).
% 1.58/0.58  fof(f333,plain,(
% 1.58/0.58    k1_xboole_0 = k4_xboole_0(sK1,sK1) | ~spl6_17),
% 1.58/0.58    inference(avatar_component_clause,[],[f331])).
% 1.58/0.58  fof(f95,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.58/0.58    inference(definition_unfolding,[],[f58,f56])).
% 1.58/0.58  fof(f56,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.58/0.58    inference(cnf_transformation,[],[f10])).
% 1.58/0.58  fof(f10,axiom,(
% 1.58/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.58/0.58  fof(f58,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f30])).
% 1.58/0.58  fof(f30,plain,(
% 1.58/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.58/0.58    inference(ennf_transformation,[],[f27])).
% 1.58/0.58  fof(f27,plain,(
% 1.58/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.58/0.58    inference(rectify,[],[f3])).
% 1.58/0.58  fof(f3,axiom,(
% 1.58/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.58/0.58  fof(f369,plain,(
% 1.58/0.58    spl6_18),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f359])).
% 1.58/0.58  fof(f359,plain,(
% 1.58/0.58    $false | spl6_18),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f47,f356,f69])).
% 1.58/0.58  fof(f69,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f8])).
% 1.58/0.58  fof(f356,plain,(
% 1.58/0.58    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | spl6_18),
% 1.58/0.58    inference(avatar_component_clause,[],[f354])).
% 1.58/0.58  fof(f354,plain,(
% 1.58/0.58    spl6_18 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.58/0.58  fof(f47,plain,(
% 1.58/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f7])).
% 1.58/0.58  fof(f7,axiom,(
% 1.58/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.58/0.58  fof(f357,plain,(
% 1.58/0.58    ~spl6_18 | ~spl6_3 | spl6_16),
% 1.58/0.58    inference(avatar_split_clause,[],[f349,f326,f129,f354])).
% 1.58/0.58  fof(f326,plain,(
% 1.58/0.58    spl6_16 <=> sK1 = k4_xboole_0(sK1,sK1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.58/0.58  fof(f349,plain,(
% 1.58/0.58    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl6_3 | spl6_16)),
% 1.58/0.58    inference(forward_demodulation,[],[f328,f130])).
% 1.58/0.58  fof(f328,plain,(
% 1.58/0.58    sK1 != k4_xboole_0(sK1,sK1) | spl6_16),
% 1.58/0.58    inference(avatar_component_clause,[],[f326])).
% 1.58/0.58  fof(f299,plain,(
% 1.58/0.58    spl6_5 | ~spl6_1 | ~spl6_10),
% 1.58/0.58    inference(avatar_split_clause,[],[f297,f230,f120,f138])).
% 1.58/0.58  fof(f120,plain,(
% 1.58/0.58    spl6_1 <=> k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.58/0.58  fof(f297,plain,(
% 1.58/0.58    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | (~spl6_1 | ~spl6_10)),
% 1.58/0.58    inference(forward_demodulation,[],[f122,f232])).
% 1.58/0.58  fof(f122,plain,(
% 1.58/0.58    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl6_1),
% 1.58/0.58    inference(avatar_component_clause,[],[f120])).
% 1.58/0.58  fof(f276,plain,(
% 1.58/0.58    ~spl6_14 | ~spl6_3 | spl6_6),
% 1.58/0.58    inference(avatar_split_clause,[],[f263,f167,f129,f273])).
% 1.58/0.58  fof(f167,plain,(
% 1.58/0.58    spl6_6 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.58/0.58  fof(f263,plain,(
% 1.58/0.58    sK2 != k2_xboole_0(k1_xboole_0,sK2) | (~spl6_3 | spl6_6)),
% 1.58/0.58    inference(forward_demodulation,[],[f169,f130])).
% 1.58/0.58  fof(f169,plain,(
% 1.58/0.58    sK2 != k2_xboole_0(sK1,sK2) | spl6_6),
% 1.58/0.58    inference(avatar_component_clause,[],[f167])).
% 1.58/0.58  fof(f260,plain,(
% 1.58/0.58    spl6_12 | ~spl6_8 | ~spl6_10),
% 1.58/0.58    inference(avatar_split_clause,[],[f241,f230,f192,f257])).
% 1.58/0.58  fof(f192,plain,(
% 1.58/0.58    spl6_8 <=> r1_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2))),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.58/0.58  fof(f241,plain,(
% 1.58/0.58    r1_xboole_0(k1_xboole_0,sK1) | (~spl6_8 | ~spl6_10)),
% 1.58/0.58    inference(backward_demodulation,[],[f194,f232])).
% 1.58/0.58  fof(f194,plain,(
% 1.58/0.58    r1_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) | ~spl6_8),
% 1.58/0.58    inference(avatar_component_clause,[],[f192])).
% 1.58/0.58  fof(f233,plain,(
% 1.58/0.58    spl6_3 | spl6_10 | ~spl6_1),
% 1.58/0.58    inference(avatar_split_clause,[],[f222,f120,f230,f129])).
% 1.58/0.58  fof(f222,plain,(
% 1.58/0.58    sK1 = k2_xboole_0(sK1,sK2) | k1_xboole_0 = sK1 | ~spl6_1),
% 1.58/0.58    inference(resolution,[],[f164,f53])).
% 1.58/0.58  fof(f53,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.58/0.58    inference(cnf_transformation,[],[f15])).
% 1.58/0.58  fof(f15,axiom,(
% 1.58/0.58    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.58/0.58  fof(f164,plain,(
% 1.58/0.58    ( ! [X9] : (~r1_tarski(X9,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X9 | k1_xboole_0 = X9) ) | ~spl6_1),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f155])).
% 1.58/0.58  fof(f155,plain,(
% 1.58/0.58    ( ! [X9] : (~r1_tarski(X9,k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X9 | k2_xboole_0(sK1,sK2) = X9 | k2_xboole_0(sK1,sK2) = X9 | k1_xboole_0 = X9) ) | ~spl6_1),
% 1.58/0.58    inference(superposition,[],[f107,f122])).
% 1.58/0.58  fof(f195,plain,(
% 1.58/0.58    spl6_8 | ~spl6_7),
% 1.58/0.58    inference(avatar_split_clause,[],[f187,f180,f192])).
% 1.58/0.58  fof(f180,plain,(
% 1.58/0.58    spl6_7 <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.58/0.58  fof(f187,plain,(
% 1.58/0.58    r1_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK2)) | ~spl6_7),
% 1.58/0.58    inference(superposition,[],[f52,f182])).
% 1.58/0.58  fof(f182,plain,(
% 1.58/0.58    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) | ~spl6_7),
% 1.58/0.58    inference(avatar_component_clause,[],[f180])).
% 1.58/0.58  fof(f52,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f14])).
% 1.58/0.58  fof(f14,axiom,(
% 1.58/0.58    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.58/0.58  fof(f183,plain,(
% 1.58/0.58    spl6_7 | ~spl6_1),
% 1.58/0.58    inference(avatar_split_clause,[],[f153,f120,f180])).
% 1.58/0.58  fof(f153,plain,(
% 1.58/0.58    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) | ~spl6_1),
% 1.58/0.58    inference(superposition,[],[f93,f122])).
% 1.58/0.58  fof(f93,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 1.58/0.58    inference(definition_unfolding,[],[f55,f87,f57])).
% 1.58/0.58  fof(f55,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.58/0.58    inference(cnf_transformation,[],[f23])).
% 1.58/0.58  fof(f23,axiom,(
% 1.58/0.58    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 1.58/0.58  fof(f170,plain,(
% 1.58/0.58    ~spl6_6 | ~spl6_1 | spl6_2),
% 1.58/0.58    inference(avatar_split_clause,[],[f142,f125,f120,f167])).
% 1.58/0.58  fof(f125,plain,(
% 1.58/0.58    spl6_2 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.58/0.58  fof(f142,plain,(
% 1.58/0.58    sK2 != k2_xboole_0(sK1,sK2) | (~spl6_1 | spl6_2)),
% 1.58/0.58    inference(superposition,[],[f127,f122])).
% 1.58/0.58  fof(f127,plain,(
% 1.58/0.58    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | spl6_2),
% 1.58/0.58    inference(avatar_component_clause,[],[f125])).
% 1.58/0.58  fof(f141,plain,(
% 1.58/0.58    ~spl6_4 | ~spl6_5),
% 1.58/0.58    inference(avatar_split_clause,[],[f91,f138,f134])).
% 1.58/0.58  fof(f91,plain,(
% 1.58/0.58    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.58/0.58    inference(definition_unfolding,[],[f42,f87])).
% 1.58/0.58  fof(f42,plain,(
% 1.58/0.58    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.58/0.58    inference(cnf_transformation,[],[f29])).
% 1.58/0.58  fof(f132,plain,(
% 1.58/0.58    ~spl6_2 | ~spl6_3),
% 1.58/0.58    inference(avatar_split_clause,[],[f90,f129,f125])).
% 1.58/0.58  fof(f90,plain,(
% 1.58/0.58    k1_xboole_0 != sK1 | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.58/0.58    inference(definition_unfolding,[],[f43,f87])).
% 1.58/0.58  fof(f43,plain,(
% 1.58/0.58    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f29])).
% 1.58/0.58  fof(f123,plain,(
% 1.58/0.58    spl6_1),
% 1.58/0.58    inference(avatar_split_clause,[],[f88,f120])).
% 1.58/0.58  fof(f88,plain,(
% 1.58/0.58    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.58/0.58    inference(definition_unfolding,[],[f45,f87])).
% 1.58/0.58  fof(f45,plain,(
% 1.58/0.58    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.58/0.58    inference(cnf_transformation,[],[f29])).
% 1.58/0.58  % SZS output end Proof for theBenchmark
% 1.58/0.58  % (20750)------------------------------
% 1.58/0.58  % (20750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (20750)Termination reason: Refutation
% 1.58/0.58  
% 1.58/0.58  % (20750)Memory used [KB]: 11129
% 1.58/0.58  % (20750)Time elapsed: 0.146 s
% 1.58/0.58  % (20750)------------------------------
% 1.58/0.58  % (20750)------------------------------
% 1.58/0.59  % (20724)Success in time 0.219 s
%------------------------------------------------------------------------------
