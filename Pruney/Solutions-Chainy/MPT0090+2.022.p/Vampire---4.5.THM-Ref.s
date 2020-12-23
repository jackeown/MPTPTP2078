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
% DateTime   : Thu Dec  3 12:31:38 EST 2020

% Result     : Theorem 6.95s
% Output     : Refutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :  210 (1102 expanded)
%              Number of leaves         :   47 ( 371 expanded)
%              Depth                    :   18
%              Number of atoms          :  436 (2141 expanded)
%              Number of equality atoms :  103 ( 656 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32996,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f66,f67,f118,f124,f130,f162,f219,f226,f262,f1764,f2617,f2784,f2805,f2810,f2815,f2820,f2904,f2964,f3531,f3969,f5171,f5176,f5181,f5186,f5191,f6376,f6381,f10738,f11671,f11676,f32962])).

fof(f32962,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f32961])).

fof(f32961,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f32960,f64])).

fof(f64,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_3
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f32960,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f31705,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f31705,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_27 ),
    inference(superposition,[],[f395,f6380])).

fof(f6380,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f6378])).

fof(f6378,plain,
    ( spl3_27
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f395,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f242,f381])).

fof(f381,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl3_1 ),
    inference(superposition,[],[f374,f110])).

fof(f110,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f99,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f99,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f90,f37])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f87,f37])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f374,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f373,f37])).

fof(f373,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f236,f367])).

fof(f367,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f74,f352,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f352,plain,(
    ! [X4,X5] : r1_tarski(k3_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f265,f328])).

fof(f328,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f327,f37])).

fof(f327,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f315,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f36,f41])).

fof(f315,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f47,f37])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f265,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f184,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f184,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f95,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f95,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f90,f41])).

fof(f74,plain,
    ( ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f57,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f57,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f54,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f54,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f236,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f242,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k3_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0) ),
    inference(superposition,[],[f46,f110])).

fof(f11676,plain,
    ( ~ spl3_30
    | ~ spl3_1
    | spl3_18 ),
    inference(avatar_split_clause,[],[f3874,f2961,f52,f11673])).

fof(f11673,plain,
    ( spl3_30
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f2961,plain,
    ( spl3_18
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f3874,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl3_1
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f74,f2963,f77])).

fof(f77,plain,(
    ! [X2,X1] :
      ( r2_xboole_0(X1,X2)
      | X1 = X2
      | k1_xboole_0 != k4_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f39,f40])).

fof(f2963,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f2961])).

fof(f11671,plain,
    ( ~ spl3_29
    | spl3_18 ),
    inference(avatar_split_clause,[],[f3867,f2961,f11668])).

fof(f11668,plain,
    ( spl3_29
  <=> r1_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f3867,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f2963,f2032])).

fof(f2032,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f213,f99])).

fof(f213,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X6,X5)
      | k1_xboole_0 = X6
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(resolution,[],[f50,f99])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f10738,plain,
    ( ~ spl3_28
    | spl3_18 ),
    inference(avatar_split_clause,[],[f3710,f2961,f10735])).

fof(f10735,plain,
    ( spl3_28
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f3710,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f38,f99,f2963,f212])).

fof(f212,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X4,X3)
      | k1_xboole_0 = X4
      | ~ r1_tarski(X4,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f50,f40])).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f6381,plain,
    ( spl3_27
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f6202,f159,f6378])).

fof(f159,plain,
    ( spl3_6
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f6202,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f161,f352,f5534,f212])).

fof(f5534,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f2950,f2039])).

fof(f2039,plain,(
    ! [X12,X13] :
      ( ~ r1_xboole_0(k2_xboole_0(X12,X13),X12)
      | k1_xboole_0 = X12 ) ),
    inference(resolution,[],[f213,f299])).

fof(f299,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f154,f40])).

fof(f154,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f144,f69])).

fof(f144,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f45,f110])).

fof(f2950,plain,(
    ! [X4,X5,X3] : r1_xboole_0(X5,k4_xboole_0(k3_xboole_0(X3,X4),X4)) ),
    inference(forward_demodulation,[],[f2925,f37])).

fof(f2925,plain,(
    ! [X4,X5,X3] : r1_xboole_0(k4_xboole_0(X5,k1_xboole_0),k4_xboole_0(k3_xboole_0(X3,X4),X4)) ),
    inference(superposition,[],[f247,f110])).

fof(f247,plain,(
    ! [X6,X4,X7,X5] : r1_xboole_0(k4_xboole_0(X7,k4_xboole_0(X4,k3_xboole_0(X5,X6))),k4_xboole_0(X4,X6)) ),
    inference(superposition,[],[f152,f46])).

fof(f152,plain,(
    ! [X10,X11,X9] : r1_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X11) ),
    inference(superposition,[],[f38,f45])).

fof(f161,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f6376,plain,
    ( spl3_26
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f6201,f59,f6373])).

fof(f6373,plain,
    ( spl3_26
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f59,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f6201,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f352,f5534,f212])).

fof(f61,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f5191,plain,
    ( ~ spl3_25
    | ~ spl3_1
    | spl3_18 ),
    inference(avatar_split_clause,[],[f3875,f2961,f52,f5188])).

fof(f5188,plain,
    ( spl3_25
  <=> r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f3875,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0)
    | ~ spl3_1
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f74,f2963,f39])).

fof(f5186,plain,
    ( spl3_24
    | spl3_18 ),
    inference(avatar_split_clause,[],[f3873,f2961,f5183])).

fof(f5183,plain,
    ( spl3_24
  <=> r2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f3873,plain,
    ( r2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f36,f2963,f39])).

fof(f5181,plain,
    ( ~ spl3_23
    | spl3_18 ),
    inference(avatar_split_clause,[],[f3857,f2961,f5178])).

fof(f5178,plain,
    ( spl3_23
  <=> r1_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f3857,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f90,f2963,f213])).

fof(f5176,plain,
    ( ~ spl3_22
    | spl3_18 ),
    inference(avatar_split_clause,[],[f3846,f2961,f5173])).

fof(f5173,plain,
    ( spl3_22
  <=> r1_tarski(k4_xboole_0(sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f3846,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK0),sK0)
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f141,f2963,f213])).

fof(f141,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f38,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f103,f37])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) ) ),
    inference(superposition,[],[f49,f37])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
      | ~ r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f5171,plain,
    ( ~ spl3_21
    | spl3_18 ),
    inference(avatar_split_clause,[],[f3770,f2961,f5168])).

fof(f5168,plain,
    ( spl3_21
  <=> r1_xboole_0(k4_xboole_0(sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f3770,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK0),sK1)
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f99,f95,f2963,f212])).

fof(f3969,plain,
    ( ~ spl3_20
    | spl3_18 ),
    inference(avatar_split_clause,[],[f3701,f2961,f3966])).

fof(f3966,plain,
    ( spl3_20
  <=> v1_xboole_0(k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f3701,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK1,sK0))
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f2963,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f79,f44])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f76,f42])).

fof(f76,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f39,f36])).

fof(f3531,plain,
    ( ~ spl3_19
    | ~ spl3_1
    | spl3_11 ),
    inference(avatar_split_clause,[],[f2766,f2614,f52,f3528])).

fof(f3528,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f2614,plain,
    ( spl3_11
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f2766,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_1
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f74,f2616,f77])).

fof(f2616,plain,
    ( k1_xboole_0 != sK1
    | spl3_11 ),
    inference(avatar_component_clause,[],[f2614])).

fof(f2964,plain,
    ( ~ spl3_18
    | ~ spl3_6
    | spl3_11 ),
    inference(avatar_split_clause,[],[f2683,f2614,f159,f2961])).

fof(f2683,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK0)
    | ~ spl3_6
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f161,f99,f2616,f212])).

fof(f2904,plain,
    ( spl3_17
    | spl3_11 ),
    inference(avatar_split_clause,[],[f2681,f2614,f2901])).

fof(f2901,plain,
    ( spl3_17
  <=> r2_hidden(sK2(k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f2681,plain,
    ( r2_hidden(sK2(k1_xboole_0,sK1),sK1)
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f2616,f79])).

fof(f2820,plain,
    ( ~ spl3_16
    | ~ spl3_1
    | spl3_11 ),
    inference(avatar_split_clause,[],[f2767,f2614,f52,f2817])).

fof(f2817,plain,
    ( spl3_16
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f2767,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_1
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f74,f2616,f39])).

fof(f2815,plain,
    ( spl3_15
    | spl3_11 ),
    inference(avatar_split_clause,[],[f2765,f2614,f2812])).

fof(f2812,plain,
    ( spl3_15
  <=> r2_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f2765,plain,
    ( r2_xboole_0(k1_xboole_0,sK1)
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f36,f2616,f39])).

fof(f2810,plain,
    ( ~ spl3_14
    | spl3_11 ),
    inference(avatar_split_clause,[],[f2759,f2614,f2807])).

fof(f2807,plain,
    ( spl3_14
  <=> r1_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f2759,plain,
    ( ~ r1_xboole_0(sK1,sK1)
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f2616,f2032])).

fof(f2805,plain,
    ( ~ spl3_13
    | ~ spl3_2
    | spl3_11 ),
    inference(avatar_split_clause,[],[f2751,f2614,f59,f2802])).

fof(f2802,plain,
    ( spl3_13
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f2751,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl3_2
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f61,f2616,f213])).

fof(f2784,plain,
    ( ~ spl3_12
    | spl3_11 ),
    inference(avatar_split_clause,[],[f2682,f2614,f2781])).

fof(f2781,plain,
    ( spl3_12
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f2682,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f2616,f83])).

fof(f2617,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f2591,f63,f52,f2614])).

fof(f2591,plain,
    ( k1_xboole_0 != sK1
    | ~ spl3_1
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f64,f2558])).

fof(f2558,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 != X2
        | k4_xboole_0(X3,X2) = X3 )
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f2516,f37])).

fof(f2516,plain,
    ( ! [X2,X3] :
        ( k4_xboole_0(X3,X2) = k4_xboole_0(X3,k1_xboole_0)
        | k1_xboole_0 != X2 )
    | ~ spl3_1 ),
    inference(superposition,[],[f420,f1497])).

fof(f1497,plain,
    ( ! [X6,X7] :
        ( k1_xboole_0 = k3_xboole_0(X6,X7)
        | k1_xboole_0 != X6 )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f1473,f74])).

fof(f1473,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != X6
      | k1_xboole_0 = k3_xboole_0(X6,X7)
      | r2_xboole_0(k3_xboole_0(X6,X7),k1_xboole_0) ) ),
    inference(resolution,[],[f1229,f39])).

fof(f1229,plain,(
    ! [X12,X13] :
      ( r1_tarski(k3_xboole_0(X12,X13),k1_xboole_0)
      | k1_xboole_0 != X12 ) ),
    inference(superposition,[],[f1200,f353])).

fof(f353,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f184,f328])).

fof(f1200,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k4_xboole_0(X1,X0))
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f1185,f37])).

fof(f1185,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(X1,X0)) ) ),
    inference(superposition,[],[f89,f37])).

fof(f89,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X4,X3)
      | r1_tarski(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4)) ) ),
    inference(resolution,[],[f48,f40])).

fof(f420,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X1))
    | ~ spl3_1 ),
    inference(superposition,[],[f380,f46])).

fof(f380,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl3_1 ),
    inference(superposition,[],[f374,f37])).

fof(f1764,plain,
    ( ~ spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f132,f115,f1761])).

fof(f1761,plain,
    ( spl3_10
  <=> r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f115,plain,
    ( spl3_4
  <=> r2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f132,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f117,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f117,plain,
    ( r2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f262,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f249,f259])).

fof(f259,plain,
    ( spl3_9
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f249,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f248,f69])).

fof(f248,plain,(
    ! [X4,X5] : k4_xboole_0(k1_xboole_0,k3_xboole_0(X4,X5)) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f238,f69])).

fof(f238,plain,(
    ! [X4,X5] : k4_xboole_0(k1_xboole_0,k3_xboole_0(X4,X5)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5)) ),
    inference(superposition,[],[f46,f69])).

fof(f226,plain,
    ( ~ spl3_8
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f220,f216,f223])).

fof(f223,plain,
    ( spl3_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f216,plain,
    ( spl3_7
  <=> r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f220,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f218,f44])).

fof(f218,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f216])).

fof(f219,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f133,f115,f216])).

fof(f133,plain,
    ( r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),sK0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f117,f42])).

fof(f162,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f142,f59,f159])).

fof(f142,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f61,f107])).

fof(f130,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f128,f60])).

fof(f60,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f128,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(superposition,[],[f38,f65])).

fof(f65,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f124,plain,
    ( ~ spl3_5
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f119,f115,f63,f121])).

fof(f121,plain,
    ( spl3_5
  <=> r2_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( ~ r2_xboole_0(sK0,sK0)
    | ~ spl3_3
    | spl3_4 ),
    inference(backward_demodulation,[],[f116,f65])).

fof(f116,plain,
    ( ~ r2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f118,plain,
    ( spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f94,f63,f115])).

fof(f94,plain,
    ( r2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f64,f90,f39])).

fof(f67,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f34,f63,f59])).

fof(f34,plain,
    ( sK0 != k4_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( sK0 != k4_xboole_0(sK0,sK1)
      | ~ r1_xboole_0(sK0,sK1) )
    & ( sK0 = k4_xboole_0(sK0,sK1)
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( sK0 != k4_xboole_0(sK0,sK1)
        | ~ r1_xboole_0(sK0,sK1) )
      & ( sK0 = k4_xboole_0(sK0,sK1)
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f66,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f33,f63,f59])).

fof(f33,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f52])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:33:54 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (31142)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (31142)Refutation not found, incomplete strategy% (31142)------------------------------
% 0.21/0.48  % (31142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31152)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (31161)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (31151)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (31142)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31142)Memory used [KB]: 10618
% 0.21/0.48  % (31142)Time elapsed: 0.059 s
% 0.21/0.48  % (31142)------------------------------
% 0.21/0.48  % (31142)------------------------------
% 0.21/0.48  % (31161)Refutation not found, incomplete strategy% (31161)------------------------------
% 0.21/0.48  % (31161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31161)Memory used [KB]: 10490
% 0.21/0.48  % (31161)Time elapsed: 0.070 s
% 0.21/0.48  % (31161)------------------------------
% 0.21/0.48  % (31161)------------------------------
% 0.21/0.49  % (31151)Refutation not found, incomplete strategy% (31151)------------------------------
% 0.21/0.49  % (31151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31151)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31151)Memory used [KB]: 6140
% 0.21/0.49  % (31151)Time elapsed: 0.073 s
% 0.21/0.49  % (31151)------------------------------
% 0.21/0.49  % (31151)------------------------------
% 0.21/0.49  % (31152)Refutation not found, incomplete strategy% (31152)------------------------------
% 0.21/0.49  % (31152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31152)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31152)Memory used [KB]: 10618
% 0.21/0.49  % (31152)Time elapsed: 0.073 s
% 0.21/0.49  % (31152)------------------------------
% 0.21/0.49  % (31152)------------------------------
% 0.21/0.49  % (31143)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (31145)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (31155)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (31160)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (31158)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (31144)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (31149)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (31159)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (31141)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (31141)Refutation not found, incomplete strategy% (31141)------------------------------
% 0.21/0.51  % (31141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31141)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31141)Memory used [KB]: 6140
% 0.21/0.51  % (31141)Time elapsed: 0.091 s
% 0.21/0.51  % (31141)------------------------------
% 0.21/0.51  % (31141)------------------------------
% 0.21/0.51  % (31150)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (31154)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (31153)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31153)Refutation not found, incomplete strategy% (31153)------------------------------
% 0.21/0.51  % (31153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31153)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31153)Memory used [KB]: 6012
% 0.21/0.51  % (31153)Time elapsed: 0.002 s
% 0.21/0.51  % (31153)------------------------------
% 0.21/0.51  % (31153)------------------------------
% 0.21/0.51  % (31146)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (31156)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (31148)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (31156)Refutation not found, incomplete strategy% (31156)------------------------------
% 0.21/0.52  % (31156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31156)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31156)Memory used [KB]: 6140
% 0.21/0.52  % (31156)Time elapsed: 0.003 s
% 0.21/0.52  % (31156)------------------------------
% 0.21/0.52  % (31156)------------------------------
% 0.21/0.52  % (31157)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (31147)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 4.37/0.93  % (31146)Time limit reached!
% 4.37/0.93  % (31146)------------------------------
% 4.37/0.93  % (31146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/0.95  % (31146)Termination reason: Time limit
% 4.58/0.95  % (31146)Termination phase: Saturation
% 4.58/0.95  
% 4.58/0.95  % (31146)Memory used [KB]: 7931
% 4.58/0.95  % (31146)Time elapsed: 0.500 s
% 4.58/0.95  % (31146)------------------------------
% 4.58/0.95  % (31146)------------------------------
% 4.58/1.02  % (31149)Time limit reached!
% 4.58/1.02  % (31149)------------------------------
% 4.58/1.02  % (31149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.02  % (31149)Termination reason: Time limit
% 4.58/1.02  
% 4.58/1.02  % (31149)Memory used [KB]: 15735
% 4.58/1.02  % (31149)Time elapsed: 0.610 s
% 4.58/1.02  % (31149)------------------------------
% 4.58/1.02  % (31149)------------------------------
% 6.95/1.27  % (31148)Refutation found. Thanks to Tanya!
% 6.95/1.27  % SZS status Theorem for theBenchmark
% 6.95/1.27  % SZS output start Proof for theBenchmark
% 6.95/1.27  fof(f32996,plain,(
% 6.95/1.27    $false),
% 6.95/1.27    inference(avatar_sat_refutation,[],[f55,f66,f67,f118,f124,f130,f162,f219,f226,f262,f1764,f2617,f2784,f2805,f2810,f2815,f2820,f2904,f2964,f3531,f3969,f5171,f5176,f5181,f5186,f5191,f6376,f6381,f10738,f11671,f11676,f32962])).
% 6.95/1.27  fof(f32962,plain,(
% 6.95/1.27    ~spl3_1 | spl3_3 | ~spl3_27),
% 6.95/1.27    inference(avatar_contradiction_clause,[],[f32961])).
% 6.95/1.27  fof(f32961,plain,(
% 6.95/1.27    $false | (~spl3_1 | spl3_3 | ~spl3_27)),
% 6.95/1.27    inference(subsumption_resolution,[],[f32960,f64])).
% 6.95/1.27  fof(f64,plain,(
% 6.95/1.27    sK0 != k4_xboole_0(sK0,sK1) | spl3_3),
% 6.95/1.27    inference(avatar_component_clause,[],[f63])).
% 6.95/1.27  fof(f63,plain,(
% 6.95/1.27    spl3_3 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 6.95/1.27  fof(f32960,plain,(
% 6.95/1.27    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_27)),
% 6.95/1.27    inference(forward_demodulation,[],[f31705,f37])).
% 6.95/1.27  fof(f37,plain,(
% 6.95/1.27    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.95/1.27    inference(cnf_transformation,[],[f7])).
% 6.95/1.27  fof(f7,axiom,(
% 6.95/1.27    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 6.95/1.27  fof(f31705,plain,(
% 6.95/1.27    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_1 | ~spl3_27)),
% 6.95/1.27    inference(superposition,[],[f395,f6380])).
% 6.95/1.27  fof(f6380,plain,(
% 6.95/1.27    k1_xboole_0 = k3_xboole_0(sK1,sK0) | ~spl3_27),
% 6.95/1.27    inference(avatar_component_clause,[],[f6378])).
% 6.95/1.27  fof(f6378,plain,(
% 6.95/1.27    spl3_27 <=> k1_xboole_0 = k3_xboole_0(sK1,sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 6.95/1.27  fof(f395,plain,(
% 6.95/1.27    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X3,X2))) ) | ~spl3_1),
% 6.95/1.27    inference(backward_demodulation,[],[f242,f381])).
% 6.95/1.27  fof(f381,plain,(
% 6.95/1.27    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl3_1),
% 6.95/1.27    inference(superposition,[],[f374,f110])).
% 6.95/1.27  fof(f110,plain,(
% 6.95/1.27    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f99,f41])).
% 6.95/1.27  fof(f41,plain,(
% 6.95/1.27    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 6.95/1.27    inference(cnf_transformation,[],[f30])).
% 6.95/1.27  fof(f30,plain,(
% 6.95/1.27    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 6.95/1.27    inference(nnf_transformation,[],[f6])).
% 6.95/1.27  fof(f6,axiom,(
% 6.95/1.27    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 6.95/1.27  fof(f99,plain,(
% 6.95/1.27    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 6.95/1.27    inference(superposition,[],[f90,f37])).
% 6.95/1.27  fof(f90,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.95/1.27    inference(forward_demodulation,[],[f87,f37])).
% 6.95/1.27  fof(f87,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0))) )),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f36,f48])).
% 6.95/1.27  fof(f48,plain,(
% 6.95/1.27    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 6.95/1.27    inference(cnf_transformation,[],[f23])).
% 6.95/1.27  fof(f23,plain,(
% 6.95/1.27    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 6.95/1.27    inference(ennf_transformation,[],[f5])).
% 6.95/1.27  fof(f5,axiom,(
% 6.95/1.27    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 6.95/1.27  fof(f36,plain,(
% 6.95/1.27    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.95/1.27    inference(cnf_transformation,[],[f4])).
% 6.95/1.27  fof(f4,axiom,(
% 6.95/1.27    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 6.95/1.27  fof(f374,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl3_1),
% 6.95/1.27    inference(forward_demodulation,[],[f373,f37])).
% 6.95/1.27  fof(f373,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_1),
% 6.95/1.27    inference(backward_demodulation,[],[f236,f367])).
% 6.95/1.27  fof(f367,plain,(
% 6.95/1.27    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl3_1),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f74,f352,f39])).
% 6.95/1.27  fof(f39,plain,(
% 6.95/1.27    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 6.95/1.27    inference(cnf_transformation,[],[f20])).
% 6.95/1.27  fof(f20,plain,(
% 6.95/1.27    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 6.95/1.27    inference(flattening,[],[f19])).
% 6.95/1.27  fof(f19,plain,(
% 6.95/1.27    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 6.95/1.27    inference(ennf_transformation,[],[f17])).
% 6.95/1.27  fof(f17,plain,(
% 6.95/1.27    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 6.95/1.27    inference(unused_predicate_definition_removal,[],[f1])).
% 6.95/1.27  fof(f1,axiom,(
% 6.95/1.27    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 6.95/1.27  fof(f352,plain,(
% 6.95/1.27    ( ! [X4,X5] : (r1_tarski(k3_xboole_0(X4,X5),X4)) )),
% 6.95/1.27    inference(superposition,[],[f265,f328])).
% 6.95/1.27  fof(f328,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 6.95/1.27    inference(forward_demodulation,[],[f327,f37])).
% 6.95/1.27  fof(f327,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.95/1.27    inference(forward_demodulation,[],[f315,f69])).
% 6.95/1.27  fof(f69,plain,(
% 6.95/1.27    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f36,f41])).
% 6.95/1.27  fof(f315,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.95/1.27    inference(superposition,[],[f47,f37])).
% 6.95/1.27  fof(f47,plain,(
% 6.95/1.27    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 6.95/1.27    inference(cnf_transformation,[],[f9])).
% 6.95/1.27  fof(f9,axiom,(
% 6.95/1.27    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 6.95/1.27  fof(f265,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f184,f40])).
% 6.95/1.27  fof(f40,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 6.95/1.27    inference(cnf_transformation,[],[f30])).
% 6.95/1.27  fof(f184,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 6.95/1.27    inference(superposition,[],[f95,f45])).
% 6.95/1.27  fof(f45,plain,(
% 6.95/1.27    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 6.95/1.27    inference(cnf_transformation,[],[f8])).
% 6.95/1.27  fof(f8,axiom,(
% 6.95/1.27    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 6.95/1.27  fof(f95,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f90,f41])).
% 6.95/1.27  fof(f74,plain,(
% 6.95/1.27    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0)) ) | ~spl3_1),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f57,f42])).
% 6.95/1.27  fof(f42,plain,(
% 6.95/1.27    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1)) )),
% 6.95/1.27    inference(cnf_transformation,[],[f32])).
% 6.95/1.27  fof(f32,plain,(
% 6.95/1.27    ! [X0,X1] : ((~r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 6.95/1.27    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f31])).
% 6.95/1.27  fof(f31,plain,(
% 6.95/1.27    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1)))),
% 6.95/1.27    introduced(choice_axiom,[])).
% 6.95/1.27  fof(f21,plain,(
% 6.95/1.27    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 6.95/1.27    inference(ennf_transformation,[],[f3])).
% 6.95/1.27  fof(f3,axiom,(
% 6.95/1.27    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 6.95/1.27  fof(f57,plain,(
% 6.95/1.27    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_1),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f54,f44])).
% 6.95/1.27  fof(f44,plain,(
% 6.95/1.27    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 6.95/1.27    inference(cnf_transformation,[],[f22])).
% 6.95/1.27  fof(f22,plain,(
% 6.95/1.27    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 6.95/1.27    inference(ennf_transformation,[],[f13])).
% 6.95/1.27  fof(f13,axiom,(
% 6.95/1.27    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 6.95/1.27  fof(f54,plain,(
% 6.95/1.27    v1_xboole_0(k1_xboole_0) | ~spl3_1),
% 6.95/1.27    inference(avatar_component_clause,[],[f52])).
% 6.95/1.27  fof(f52,plain,(
% 6.95/1.27    spl3_1 <=> v1_xboole_0(k1_xboole_0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 6.95/1.27  fof(f236,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(k1_xboole_0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.95/1.27    inference(superposition,[],[f46,f37])).
% 6.95/1.27  fof(f46,plain,(
% 6.95/1.27    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 6.95/1.27    inference(cnf_transformation,[],[f10])).
% 6.95/1.27  fof(f10,axiom,(
% 6.95/1.27    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).
% 6.95/1.27  fof(f242,plain,(
% 6.95/1.27    ( ! [X2,X3] : (k4_xboole_0(X2,k3_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) )),
% 6.95/1.27    inference(superposition,[],[f46,f110])).
% 6.95/1.27  fof(f11676,plain,(
% 6.95/1.27    ~spl3_30 | ~spl3_1 | spl3_18),
% 6.95/1.27    inference(avatar_split_clause,[],[f3874,f2961,f52,f11673])).
% 6.95/1.27  fof(f11673,plain,(
% 6.95/1.27    spl3_30 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 6.95/1.27  fof(f2961,plain,(
% 6.95/1.27    spl3_18 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 6.95/1.27  fof(f3874,plain,(
% 6.95/1.27    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) | (~spl3_1 | spl3_18)),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f74,f2963,f77])).
% 6.95/1.27  fof(f77,plain,(
% 6.95/1.27    ( ! [X2,X1] : (r2_xboole_0(X1,X2) | X1 = X2 | k1_xboole_0 != k4_xboole_0(X1,X2)) )),
% 6.95/1.27    inference(resolution,[],[f39,f40])).
% 6.95/1.27  fof(f2963,plain,(
% 6.95/1.27    k1_xboole_0 != k4_xboole_0(sK1,sK0) | spl3_18),
% 6.95/1.27    inference(avatar_component_clause,[],[f2961])).
% 6.95/1.27  fof(f11671,plain,(
% 6.95/1.27    ~spl3_29 | spl3_18),
% 6.95/1.27    inference(avatar_split_clause,[],[f3867,f2961,f11668])).
% 6.95/1.27  fof(f11668,plain,(
% 6.95/1.27    spl3_29 <=> r1_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0))),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 6.95/1.27  fof(f3867,plain,(
% 6.95/1.27    ~r1_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,sK0)) | spl3_18),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f2963,f2032])).
% 6.95/1.27  fof(f2032,plain,(
% 6.95/1.27    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 6.95/1.27    inference(resolution,[],[f213,f99])).
% 6.95/1.27  fof(f213,plain,(
% 6.95/1.27    ( ! [X6,X5] : (~r1_tarski(X6,X5) | k1_xboole_0 = X6 | ~r1_xboole_0(X5,X6)) )),
% 6.95/1.27    inference(resolution,[],[f50,f99])).
% 6.95/1.27  fof(f50,plain,(
% 6.95/1.27    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 6.95/1.27    inference(cnf_transformation,[],[f26])).
% 6.95/1.27  fof(f26,plain,(
% 6.95/1.27    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 6.95/1.27    inference(flattening,[],[f25])).
% 6.95/1.27  fof(f25,plain,(
% 6.95/1.27    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 6.95/1.27    inference(ennf_transformation,[],[f11])).
% 6.95/1.27  fof(f11,axiom,(
% 6.95/1.27    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 6.95/1.27  fof(f10738,plain,(
% 6.95/1.27    ~spl3_28 | spl3_18),
% 6.95/1.27    inference(avatar_split_clause,[],[f3710,f2961,f10735])).
% 6.95/1.27  fof(f10735,plain,(
% 6.95/1.27    spl3_28 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 6.95/1.27  fof(f3710,plain,(
% 6.95/1.27    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK1,sK0),sK0) | spl3_18),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f38,f99,f2963,f212])).
% 6.95/1.27  fof(f212,plain,(
% 6.95/1.27    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(X4,X3) | k1_xboole_0 = X4 | ~r1_tarski(X4,X2) | ~r1_xboole_0(X2,X3)) )),
% 6.95/1.27    inference(resolution,[],[f50,f40])).
% 6.95/1.27  fof(f38,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 6.95/1.27    inference(cnf_transformation,[],[f12])).
% 6.95/1.27  fof(f12,axiom,(
% 6.95/1.27    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 6.95/1.27  fof(f6381,plain,(
% 6.95/1.27    spl3_27 | ~spl3_6),
% 6.95/1.27    inference(avatar_split_clause,[],[f6202,f159,f6378])).
% 6.95/1.27  fof(f159,plain,(
% 6.95/1.27    spl3_6 <=> r1_xboole_0(sK1,sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 6.95/1.27  fof(f6202,plain,(
% 6.95/1.27    k1_xboole_0 = k3_xboole_0(sK1,sK0) | ~spl3_6),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f161,f352,f5534,f212])).
% 6.95/1.27  fof(f5534,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f2950,f2039])).
% 6.95/1.27  fof(f2039,plain,(
% 6.95/1.27    ( ! [X12,X13] : (~r1_xboole_0(k2_xboole_0(X12,X13),X12) | k1_xboole_0 = X12) )),
% 6.95/1.27    inference(resolution,[],[f213,f299])).
% 6.95/1.27  fof(f299,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f154,f40])).
% 6.95/1.27  fof(f154,plain,(
% 6.95/1.27    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 6.95/1.27    inference(forward_demodulation,[],[f144,f69])).
% 6.95/1.27  fof(f144,plain,(
% 6.95/1.27    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 6.95/1.27    inference(superposition,[],[f45,f110])).
% 6.95/1.27  fof(f2950,plain,(
% 6.95/1.27    ( ! [X4,X5,X3] : (r1_xboole_0(X5,k4_xboole_0(k3_xboole_0(X3,X4),X4))) )),
% 6.95/1.27    inference(forward_demodulation,[],[f2925,f37])).
% 6.95/1.27  fof(f2925,plain,(
% 6.95/1.27    ( ! [X4,X5,X3] : (r1_xboole_0(k4_xboole_0(X5,k1_xboole_0),k4_xboole_0(k3_xboole_0(X3,X4),X4))) )),
% 6.95/1.27    inference(superposition,[],[f247,f110])).
% 6.95/1.27  fof(f247,plain,(
% 6.95/1.27    ( ! [X6,X4,X7,X5] : (r1_xboole_0(k4_xboole_0(X7,k4_xboole_0(X4,k3_xboole_0(X5,X6))),k4_xboole_0(X4,X6))) )),
% 6.95/1.27    inference(superposition,[],[f152,f46])).
% 6.95/1.27  fof(f152,plain,(
% 6.95/1.27    ( ! [X10,X11,X9] : (r1_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X11)) )),
% 6.95/1.27    inference(superposition,[],[f38,f45])).
% 6.95/1.27  fof(f161,plain,(
% 6.95/1.27    r1_xboole_0(sK1,sK0) | ~spl3_6),
% 6.95/1.27    inference(avatar_component_clause,[],[f159])).
% 6.95/1.27  fof(f6376,plain,(
% 6.95/1.27    spl3_26 | ~spl3_2),
% 6.95/1.27    inference(avatar_split_clause,[],[f6201,f59,f6373])).
% 6.95/1.27  fof(f6373,plain,(
% 6.95/1.27    spl3_26 <=> k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 6.95/1.27  fof(f59,plain,(
% 6.95/1.27    spl3_2 <=> r1_xboole_0(sK0,sK1)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 6.95/1.27  fof(f6201,plain,(
% 6.95/1.27    k1_xboole_0 = k3_xboole_0(sK0,sK1) | ~spl3_2),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f61,f352,f5534,f212])).
% 6.95/1.27  fof(f61,plain,(
% 6.95/1.27    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 6.95/1.27    inference(avatar_component_clause,[],[f59])).
% 6.95/1.27  fof(f5191,plain,(
% 6.95/1.27    ~spl3_25 | ~spl3_1 | spl3_18),
% 6.95/1.27    inference(avatar_split_clause,[],[f3875,f2961,f52,f5188])).
% 6.95/1.27  fof(f5188,plain,(
% 6.95/1.27    spl3_25 <=> r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 6.95/1.27  fof(f3875,plain,(
% 6.95/1.27    ~r1_tarski(k4_xboole_0(sK1,sK0),k1_xboole_0) | (~spl3_1 | spl3_18)),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f74,f2963,f39])).
% 6.95/1.27  fof(f5186,plain,(
% 6.95/1.27    spl3_24 | spl3_18),
% 6.95/1.27    inference(avatar_split_clause,[],[f3873,f2961,f5183])).
% 6.95/1.27  fof(f5183,plain,(
% 6.95/1.27    spl3_24 <=> r2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0))),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 6.95/1.27  fof(f3873,plain,(
% 6.95/1.27    r2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK0)) | spl3_18),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f36,f2963,f39])).
% 6.95/1.27  fof(f5181,plain,(
% 6.95/1.27    ~spl3_23 | spl3_18),
% 6.95/1.27    inference(avatar_split_clause,[],[f3857,f2961,f5178])).
% 6.95/1.27  fof(f5178,plain,(
% 6.95/1.27    spl3_23 <=> r1_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 6.95/1.27  fof(f3857,plain,(
% 6.95/1.27    ~r1_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | spl3_18),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f90,f2963,f213])).
% 6.95/1.27  fof(f5176,plain,(
% 6.95/1.27    ~spl3_22 | spl3_18),
% 6.95/1.27    inference(avatar_split_clause,[],[f3846,f2961,f5173])).
% 6.95/1.27  fof(f5173,plain,(
% 6.95/1.27    spl3_22 <=> r1_tarski(k4_xboole_0(sK1,sK0),sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 6.95/1.27  fof(f3846,plain,(
% 6.95/1.27    ~r1_tarski(k4_xboole_0(sK1,sK0),sK0) | spl3_18),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f141,f2963,f213])).
% 6.95/1.27  fof(f141,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f38,f107])).
% 6.95/1.27  fof(f107,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 6.95/1.27    inference(forward_demodulation,[],[f103,f37])).
% 6.95/1.27  fof(f103,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0))) )),
% 6.95/1.27    inference(superposition,[],[f49,f37])).
% 6.95/1.27  fof(f49,plain,(
% 6.95/1.27    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 6.95/1.27    inference(cnf_transformation,[],[f24])).
% 6.95/1.27  fof(f24,plain,(
% 6.95/1.27    ! [X0,X1,X2] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 6.95/1.27    inference(ennf_transformation,[],[f14])).
% 6.95/1.27  fof(f14,axiom,(
% 6.95/1.27    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 6.95/1.27  fof(f5171,plain,(
% 6.95/1.27    ~spl3_21 | spl3_18),
% 6.95/1.27    inference(avatar_split_clause,[],[f3770,f2961,f5168])).
% 6.95/1.27  fof(f5168,plain,(
% 6.95/1.27    spl3_21 <=> r1_xboole_0(k4_xboole_0(sK1,sK0),sK1)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 6.95/1.27  fof(f3770,plain,(
% 6.95/1.27    ~r1_xboole_0(k4_xboole_0(sK1,sK0),sK1) | spl3_18),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f99,f95,f2963,f212])).
% 6.95/1.27  fof(f3969,plain,(
% 6.95/1.27    ~spl3_20 | spl3_18),
% 6.95/1.27    inference(avatar_split_clause,[],[f3701,f2961,f3966])).
% 6.95/1.27  fof(f3966,plain,(
% 6.95/1.27    spl3_20 <=> v1_xboole_0(k4_xboole_0(sK1,sK0))),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 6.95/1.27  fof(f3701,plain,(
% 6.95/1.27    ~v1_xboole_0(k4_xboole_0(sK1,sK0)) | spl3_18),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f2963,f83])).
% 6.95/1.27  fof(f83,plain,(
% 6.95/1.27    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 6.95/1.27    inference(resolution,[],[f79,f44])).
% 6.95/1.27  fof(f79,plain,(
% 6.95/1.27    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) )),
% 6.95/1.27    inference(resolution,[],[f76,f42])).
% 6.95/1.27  fof(f76,plain,(
% 6.95/1.27    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 6.95/1.27    inference(resolution,[],[f39,f36])).
% 6.95/1.27  fof(f3531,plain,(
% 6.95/1.27    ~spl3_19 | ~spl3_1 | spl3_11),
% 6.95/1.27    inference(avatar_split_clause,[],[f2766,f2614,f52,f3528])).
% 6.95/1.27  fof(f3528,plain,(
% 6.95/1.27    spl3_19 <=> k1_xboole_0 = k4_xboole_0(sK1,k1_xboole_0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 6.95/1.27  fof(f2614,plain,(
% 6.95/1.27    spl3_11 <=> k1_xboole_0 = sK1),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 6.95/1.27  fof(f2766,plain,(
% 6.95/1.27    k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0) | (~spl3_1 | spl3_11)),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f74,f2616,f77])).
% 6.95/1.27  fof(f2616,plain,(
% 6.95/1.27    k1_xboole_0 != sK1 | spl3_11),
% 6.95/1.27    inference(avatar_component_clause,[],[f2614])).
% 6.95/1.27  fof(f2964,plain,(
% 6.95/1.27    ~spl3_18 | ~spl3_6 | spl3_11),
% 6.95/1.27    inference(avatar_split_clause,[],[f2683,f2614,f159,f2961])).
% 6.95/1.27  fof(f2683,plain,(
% 6.95/1.27    k1_xboole_0 != k4_xboole_0(sK1,sK0) | (~spl3_6 | spl3_11)),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f161,f99,f2616,f212])).
% 6.95/1.27  fof(f2904,plain,(
% 6.95/1.27    spl3_17 | spl3_11),
% 6.95/1.27    inference(avatar_split_clause,[],[f2681,f2614,f2901])).
% 6.95/1.27  fof(f2901,plain,(
% 6.95/1.27    spl3_17 <=> r2_hidden(sK2(k1_xboole_0,sK1),sK1)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 6.95/1.27  fof(f2681,plain,(
% 6.95/1.27    r2_hidden(sK2(k1_xboole_0,sK1),sK1) | spl3_11),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f2616,f79])).
% 6.95/1.27  fof(f2820,plain,(
% 6.95/1.27    ~spl3_16 | ~spl3_1 | spl3_11),
% 6.95/1.27    inference(avatar_split_clause,[],[f2767,f2614,f52,f2817])).
% 6.95/1.27  fof(f2817,plain,(
% 6.95/1.27    spl3_16 <=> r1_tarski(sK1,k1_xboole_0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 6.95/1.27  fof(f2767,plain,(
% 6.95/1.27    ~r1_tarski(sK1,k1_xboole_0) | (~spl3_1 | spl3_11)),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f74,f2616,f39])).
% 6.95/1.27  fof(f2815,plain,(
% 6.95/1.27    spl3_15 | spl3_11),
% 6.95/1.27    inference(avatar_split_clause,[],[f2765,f2614,f2812])).
% 6.95/1.27  fof(f2812,plain,(
% 6.95/1.27    spl3_15 <=> r2_xboole_0(k1_xboole_0,sK1)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 6.95/1.27  fof(f2765,plain,(
% 6.95/1.27    r2_xboole_0(k1_xboole_0,sK1) | spl3_11),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f36,f2616,f39])).
% 6.95/1.27  fof(f2810,plain,(
% 6.95/1.27    ~spl3_14 | spl3_11),
% 6.95/1.27    inference(avatar_split_clause,[],[f2759,f2614,f2807])).
% 6.95/1.27  fof(f2807,plain,(
% 6.95/1.27    spl3_14 <=> r1_xboole_0(sK1,sK1)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 6.95/1.27  fof(f2759,plain,(
% 6.95/1.27    ~r1_xboole_0(sK1,sK1) | spl3_11),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f2616,f2032])).
% 6.95/1.27  fof(f2805,plain,(
% 6.95/1.27    ~spl3_13 | ~spl3_2 | spl3_11),
% 6.95/1.27    inference(avatar_split_clause,[],[f2751,f2614,f59,f2802])).
% 6.95/1.27  fof(f2802,plain,(
% 6.95/1.27    spl3_13 <=> r1_tarski(sK1,sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 6.95/1.27  fof(f2751,plain,(
% 6.95/1.27    ~r1_tarski(sK1,sK0) | (~spl3_2 | spl3_11)),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f61,f2616,f213])).
% 6.95/1.27  fof(f2784,plain,(
% 6.95/1.27    ~spl3_12 | spl3_11),
% 6.95/1.27    inference(avatar_split_clause,[],[f2682,f2614,f2781])).
% 6.95/1.27  fof(f2781,plain,(
% 6.95/1.27    spl3_12 <=> v1_xboole_0(sK1)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 6.95/1.27  fof(f2682,plain,(
% 6.95/1.27    ~v1_xboole_0(sK1) | spl3_11),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f2616,f83])).
% 6.95/1.27  fof(f2617,plain,(
% 6.95/1.27    ~spl3_11 | ~spl3_1 | spl3_3),
% 6.95/1.27    inference(avatar_split_clause,[],[f2591,f63,f52,f2614])).
% 6.95/1.27  fof(f2591,plain,(
% 6.95/1.27    k1_xboole_0 != sK1 | (~spl3_1 | spl3_3)),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f64,f2558])).
% 6.95/1.27  fof(f2558,plain,(
% 6.95/1.27    ( ! [X2,X3] : (k1_xboole_0 != X2 | k4_xboole_0(X3,X2) = X3) ) | ~spl3_1),
% 6.95/1.27    inference(forward_demodulation,[],[f2516,f37])).
% 6.95/1.27  fof(f2516,plain,(
% 6.95/1.27    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(X3,k1_xboole_0) | k1_xboole_0 != X2) ) | ~spl3_1),
% 6.95/1.27    inference(superposition,[],[f420,f1497])).
% 6.95/1.27  fof(f1497,plain,(
% 6.95/1.27    ( ! [X6,X7] : (k1_xboole_0 = k3_xboole_0(X6,X7) | k1_xboole_0 != X6) ) | ~spl3_1),
% 6.95/1.27    inference(subsumption_resolution,[],[f1473,f74])).
% 6.95/1.27  fof(f1473,plain,(
% 6.95/1.27    ( ! [X6,X7] : (k1_xboole_0 != X6 | k1_xboole_0 = k3_xboole_0(X6,X7) | r2_xboole_0(k3_xboole_0(X6,X7),k1_xboole_0)) )),
% 6.95/1.27    inference(resolution,[],[f1229,f39])).
% 6.95/1.27  fof(f1229,plain,(
% 6.95/1.27    ( ! [X12,X13] : (r1_tarski(k3_xboole_0(X12,X13),k1_xboole_0) | k1_xboole_0 != X12) )),
% 6.95/1.27    inference(superposition,[],[f1200,f353])).
% 6.95/1.27  fof(f353,plain,(
% 6.95/1.27    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6)) )),
% 6.95/1.27    inference(superposition,[],[f184,f328])).
% 6.95/1.27  fof(f1200,plain,(
% 6.95/1.27    ( ! [X0,X1] : (r1_tarski(X1,k4_xboole_0(X1,X0)) | k1_xboole_0 != X0) )),
% 6.95/1.27    inference(forward_demodulation,[],[f1185,f37])).
% 6.95/1.27  fof(f1185,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(X1,X0))) )),
% 6.95/1.27    inference(superposition,[],[f89,f37])).
% 6.95/1.27  fof(f89,plain,(
% 6.95/1.27    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(X4,X3) | r1_tarski(k4_xboole_0(X2,X3),k4_xboole_0(X2,X4))) )),
% 6.95/1.27    inference(resolution,[],[f48,f40])).
% 6.95/1.27  fof(f420,plain,(
% 6.95/1.27    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X1))) ) | ~spl3_1),
% 6.95/1.27    inference(superposition,[],[f380,f46])).
% 6.95/1.27  fof(f380,plain,(
% 6.95/1.27    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl3_1),
% 6.95/1.27    inference(superposition,[],[f374,f37])).
% 6.95/1.27  fof(f1764,plain,(
% 6.95/1.27    ~spl3_10 | ~spl3_4),
% 6.95/1.27    inference(avatar_split_clause,[],[f132,f115,f1761])).
% 6.95/1.27  fof(f1761,plain,(
% 6.95/1.27    spl3_10 <=> r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1))),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 6.95/1.27  fof(f115,plain,(
% 6.95/1.27    spl3_4 <=> r2_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 6.95/1.27  fof(f132,plain,(
% 6.95/1.27    ~r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1)) | ~spl3_4),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f117,f43])).
% 6.95/1.27  fof(f43,plain,(
% 6.95/1.27    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 6.95/1.27    inference(cnf_transformation,[],[f32])).
% 6.95/1.27  fof(f117,plain,(
% 6.95/1.27    r2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl3_4),
% 6.95/1.27    inference(avatar_component_clause,[],[f115])).
% 6.95/1.27  fof(f262,plain,(
% 6.95/1.27    spl3_9),
% 6.95/1.27    inference(avatar_split_clause,[],[f249,f259])).
% 6.95/1.27  fof(f259,plain,(
% 6.95/1.27    spl3_9 <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 6.95/1.27  fof(f249,plain,(
% 6.95/1.27    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 6.95/1.27    inference(forward_demodulation,[],[f248,f69])).
% 6.95/1.27  fof(f248,plain,(
% 6.95/1.27    ( ! [X4,X5] : (k4_xboole_0(k1_xboole_0,k3_xboole_0(X4,X5)) = k2_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 6.95/1.27    inference(forward_demodulation,[],[f238,f69])).
% 6.95/1.27  fof(f238,plain,(
% 6.95/1.27    ( ! [X4,X5] : (k4_xboole_0(k1_xboole_0,k3_xboole_0(X4,X5)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5))) )),
% 6.95/1.27    inference(superposition,[],[f46,f69])).
% 6.95/1.27  fof(f226,plain,(
% 6.95/1.27    ~spl3_8 | ~spl3_7),
% 6.95/1.27    inference(avatar_split_clause,[],[f220,f216,f223])).
% 6.95/1.27  fof(f223,plain,(
% 6.95/1.27    spl3_8 <=> v1_xboole_0(sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 6.95/1.27  fof(f216,plain,(
% 6.95/1.27    spl3_7 <=> r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 6.95/1.27  fof(f220,plain,(
% 6.95/1.27    ~v1_xboole_0(sK0) | ~spl3_7),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f218,f44])).
% 6.95/1.27  fof(f218,plain,(
% 6.95/1.27    r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),sK0) | ~spl3_7),
% 6.95/1.27    inference(avatar_component_clause,[],[f216])).
% 6.95/1.27  fof(f219,plain,(
% 6.95/1.27    spl3_7 | ~spl3_4),
% 6.95/1.27    inference(avatar_split_clause,[],[f133,f115,f216])).
% 6.95/1.27  fof(f133,plain,(
% 6.95/1.27    r2_hidden(sK2(k4_xboole_0(sK0,sK1),sK0),sK0) | ~spl3_4),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f117,f42])).
% 6.95/1.27  fof(f162,plain,(
% 6.95/1.27    spl3_6 | ~spl3_2),
% 6.95/1.27    inference(avatar_split_clause,[],[f142,f59,f159])).
% 6.95/1.27  fof(f142,plain,(
% 6.95/1.27    r1_xboole_0(sK1,sK0) | ~spl3_2),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f61,f107])).
% 6.95/1.27  fof(f130,plain,(
% 6.95/1.27    spl3_2 | ~spl3_3),
% 6.95/1.27    inference(avatar_contradiction_clause,[],[f129])).
% 6.95/1.27  fof(f129,plain,(
% 6.95/1.27    $false | (spl3_2 | ~spl3_3)),
% 6.95/1.27    inference(subsumption_resolution,[],[f128,f60])).
% 6.95/1.27  fof(f60,plain,(
% 6.95/1.27    ~r1_xboole_0(sK0,sK1) | spl3_2),
% 6.95/1.27    inference(avatar_component_clause,[],[f59])).
% 6.95/1.27  fof(f128,plain,(
% 6.95/1.27    r1_xboole_0(sK0,sK1) | ~spl3_3),
% 6.95/1.27    inference(superposition,[],[f38,f65])).
% 6.95/1.27  fof(f65,plain,(
% 6.95/1.27    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_3),
% 6.95/1.27    inference(avatar_component_clause,[],[f63])).
% 6.95/1.27  fof(f124,plain,(
% 6.95/1.27    ~spl3_5 | ~spl3_3 | spl3_4),
% 6.95/1.27    inference(avatar_split_clause,[],[f119,f115,f63,f121])).
% 6.95/1.27  fof(f121,plain,(
% 6.95/1.27    spl3_5 <=> r2_xboole_0(sK0,sK0)),
% 6.95/1.27    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 6.95/1.27  fof(f119,plain,(
% 6.95/1.27    ~r2_xboole_0(sK0,sK0) | (~spl3_3 | spl3_4)),
% 6.95/1.27    inference(backward_demodulation,[],[f116,f65])).
% 6.95/1.27  fof(f116,plain,(
% 6.95/1.27    ~r2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | spl3_4),
% 6.95/1.27    inference(avatar_component_clause,[],[f115])).
% 6.95/1.27  fof(f118,plain,(
% 6.95/1.27    spl3_4 | spl3_3),
% 6.95/1.27    inference(avatar_split_clause,[],[f94,f63,f115])).
% 6.95/1.27  fof(f94,plain,(
% 6.95/1.27    r2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | spl3_3),
% 6.95/1.27    inference(unit_resulting_resolution,[],[f64,f90,f39])).
% 6.95/1.27  fof(f67,plain,(
% 6.95/1.27    ~spl3_2 | ~spl3_3),
% 6.95/1.27    inference(avatar_split_clause,[],[f34,f63,f59])).
% 6.95/1.27  fof(f34,plain,(
% 6.95/1.27    sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 6.95/1.27    inference(cnf_transformation,[],[f29])).
% 6.95/1.27  fof(f29,plain,(
% 6.95/1.27    (sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1))),
% 6.95/1.27    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 6.95/1.27  fof(f28,plain,(
% 6.95/1.27    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((sK0 != k4_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)) & (sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)))),
% 6.95/1.27    introduced(choice_axiom,[])).
% 6.95/1.27  fof(f27,plain,(
% 6.95/1.27    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 6.95/1.27    inference(nnf_transformation,[],[f18])).
% 6.95/1.27  fof(f18,plain,(
% 6.95/1.27    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 6.95/1.27    inference(ennf_transformation,[],[f16])).
% 6.95/1.27  fof(f16,negated_conjecture,(
% 6.95/1.27    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 6.95/1.27    inference(negated_conjecture,[],[f15])).
% 6.95/1.27  fof(f15,conjecture,(
% 6.95/1.27    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 6.95/1.27  fof(f66,plain,(
% 6.95/1.27    spl3_2 | spl3_3),
% 6.95/1.27    inference(avatar_split_clause,[],[f33,f63,f59])).
% 6.95/1.27  fof(f33,plain,(
% 6.95/1.27    sK0 = k4_xboole_0(sK0,sK1) | r1_xboole_0(sK0,sK1)),
% 6.95/1.27    inference(cnf_transformation,[],[f29])).
% 6.95/1.27  fof(f55,plain,(
% 6.95/1.27    spl3_1),
% 6.95/1.27    inference(avatar_split_clause,[],[f35,f52])).
% 6.95/1.27  fof(f35,plain,(
% 6.95/1.27    v1_xboole_0(k1_xboole_0)),
% 6.95/1.27    inference(cnf_transformation,[],[f2])).
% 6.95/1.27  fof(f2,axiom,(
% 6.95/1.27    v1_xboole_0(k1_xboole_0)),
% 6.95/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 6.95/1.27  % SZS output end Proof for theBenchmark
% 6.95/1.27  % (31148)------------------------------
% 6.95/1.27  % (31148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.95/1.27  % (31148)Termination reason: Refutation
% 6.95/1.27  
% 6.95/1.27  % (31148)Memory used [KB]: 19957
% 6.95/1.27  % (31148)Time elapsed: 0.849 s
% 6.95/1.27  % (31148)------------------------------
% 6.95/1.27  % (31148)------------------------------
% 6.95/1.28  % (31140)Success in time 0.914 s
%------------------------------------------------------------------------------
