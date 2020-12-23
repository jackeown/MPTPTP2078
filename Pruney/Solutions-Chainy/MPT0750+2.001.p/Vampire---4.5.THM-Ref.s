%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:39 EST 2020

% Result     : Theorem 3.20s
% Output     : Refutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 400 expanded)
%              Number of leaves         :   47 ( 143 expanded)
%              Depth                    :   11
%              Number of atoms          :  690 (1624 expanded)
%              Number of equality atoms :   68 ( 151 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4301,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f127,f132,f137,f141,f146,f383,f400,f422,f528,f685,f701,f2227,f2228,f2289,f2368,f2679,f2697,f2708,f3922,f4043,f4300])).

fof(f4300,plain,
    ( ~ spl8_1
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f4299])).

fof(f4299,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f4298,f121])).

fof(f121,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_1
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f4298,plain,
    ( ~ v4_ordinal1(sK0)
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f4294,f154])).

fof(f154,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(resolution,[],[f83,f117])).

fof(f117,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f4294,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v4_ordinal1(sK0)
    | ~ spl8_8 ),
    inference(superposition,[],[f377,f98])).

fof(f98,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).

fof(f377,plain,
    ( r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl8_8
  <=> r2_hidden(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f4043,plain,
    ( ~ spl8_19
    | spl8_134 ),
    inference(avatar_contradiction_clause,[],[f4042])).

fof(f4042,plain,
    ( $false
    | ~ spl8_19
    | spl8_134 ),
    inference(subsumption_resolution,[],[f4038,f684])).

fof(f684,plain,
    ( v1_ordinal1(sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f682])).

fof(f682,plain,
    ( spl8_19
  <=> v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f4038,plain,
    ( ~ v1_ordinal1(sK1)
    | spl8_134 ),
    inference(resolution,[],[f3921,f912])).

fof(f912,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(X0),X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f908])).

fof(f908,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(X0),X0)
      | ~ v1_ordinal1(X0)
      | r1_tarski(k3_tarski(X0),X0) ) ),
    inference(resolution,[],[f206,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK6(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f206,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK6(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(resolution,[],[f90,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f3921,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK1)
    | spl8_134 ),
    inference(avatar_component_clause,[],[f3919])).

fof(f3919,plain,
    ( spl8_134
  <=> r1_tarski(k3_tarski(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).

fof(f3922,plain,
    ( ~ spl8_134
    | ~ spl8_11
    | spl8_23
    | ~ spl8_81 ),
    inference(avatar_split_clause,[],[f3917,f2271,f741,f397,f3919])).

fof(f397,plain,
    ( spl8_11
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f741,plain,
    ( spl8_23
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f2271,plain,
    ( spl8_81
  <=> sK0 = k1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f3917,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK1)
    | ~ spl8_11
    | spl8_23
    | ~ spl8_81 ),
    inference(subsumption_resolution,[],[f3916,f742])).

fof(f742,plain,
    ( sK0 != sK1
    | spl8_23 ),
    inference(avatar_component_clause,[],[f741])).

fof(f3916,plain,
    ( sK0 = sK1
    | ~ r1_tarski(k3_tarski(sK1),sK1)
    | ~ spl8_11
    | ~ spl8_81 ),
    inference(forward_demodulation,[],[f3880,f399])).

fof(f399,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f397])).

fof(f3880,plain,
    ( sK1 = k3_tarski(sK0)
    | ~ r1_tarski(k3_tarski(sK1),sK1)
    | ~ spl8_81 ),
    inference(superposition,[],[f1209,f2273])).

fof(f2273,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ spl8_81 ),
    inference(avatar_component_clause,[],[f2271])).

fof(f1209,plain,(
    ! [X0] :
      ( k3_tarski(k1_ordinal1(X0)) = X0
      | ~ r1_tarski(k3_tarski(X0),X0) ) ),
    inference(forward_demodulation,[],[f1208,f106])).

fof(f106,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f1208,plain,(
    ! [X0] :
      ( k3_tarski(k1_ordinal1(X0)) = X0
      | ~ r1_tarski(k3_tarski(X0),k3_tarski(k1_tarski(X0))) ) ),
    inference(forward_demodulation,[],[f1174,f106])).

fof(f1174,plain,(
    ! [X0] :
      ( k3_tarski(k1_tarski(X0)) = k3_tarski(k1_ordinal1(X0))
      | ~ r1_tarski(k3_tarski(X0),k3_tarski(k1_tarski(X0))) ) ),
    inference(superposition,[],[f235,f74])).

fof(f74,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f235,plain,(
    ! [X2,X3] :
      ( k3_tarski(X3) = k3_tarski(k2_xboole_0(X2,X3))
      | ~ r1_tarski(k3_tarski(X2),k3_tarski(X3)) ) ),
    inference(superposition,[],[f104,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f104,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f2708,plain,
    ( spl8_81
    | spl8_2
    | ~ spl8_6
    | ~ spl8_79
    | spl8_80 ),
    inference(avatar_split_clause,[],[f2707,f2267,f2263,f143,f124,f2271])).

fof(f124,plain,
    ( spl8_2
  <=> r2_hidden(k1_ordinal1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f143,plain,
    ( spl8_6
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f2263,plain,
    ( spl8_79
  <=> v3_ordinal1(k1_ordinal1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f2267,plain,
    ( spl8_80
  <=> r2_hidden(sK0,k1_ordinal1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f2707,plain,
    ( sK0 = k1_ordinal1(sK1)
    | spl8_2
    | ~ spl8_6
    | ~ spl8_79
    | spl8_80 ),
    inference(subsumption_resolution,[],[f2706,f2264])).

fof(f2264,plain,
    ( v3_ordinal1(k1_ordinal1(sK1))
    | ~ spl8_79 ),
    inference(avatar_component_clause,[],[f2263])).

fof(f2706,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v3_ordinal1(k1_ordinal1(sK1))
    | spl8_2
    | ~ spl8_6
    | spl8_80 ),
    inference(subsumption_resolution,[],[f2705,f145])).

fof(f145,plain,
    ( v3_ordinal1(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f2705,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK1))
    | spl8_2
    | spl8_80 ),
    inference(subsumption_resolution,[],[f2703,f126])).

fof(f126,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f2703,plain,
    ( sK0 = k1_ordinal1(sK1)
    | r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(k1_ordinal1(sK1))
    | spl8_80 ),
    inference(resolution,[],[f2268,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f2268,plain,
    ( ~ r2_hidden(sK0,k1_ordinal1(sK1))
    | spl8_80 ),
    inference(avatar_component_clause,[],[f2267])).

fof(f2697,plain,
    ( ~ spl8_3
    | ~ spl8_86 ),
    inference(avatar_contradiction_clause,[],[f2686])).

fof(f2686,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f131,f154,f2314,f252])).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(superposition,[],[f114,f106])).

fof(f114,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK3(X0,X1),X3) )
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( ( r2_hidden(sK4(X0,X1),X0)
              & r2_hidden(sK3(X0,X1),sK4(X0,X1)) )
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK5(X0,X5),X0)
                & r2_hidden(X5,sK5(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f56,f59,f58,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK3(X0,X1),X3) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK3(X0,X1),X4) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK3(X0,X1),X4) )
     => ( r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK5(X0,X5),X0)
        & r2_hidden(X5,sK5(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f2314,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl8_86 ),
    inference(avatar_component_clause,[],[f2312])).

fof(f2312,plain,
    ( spl8_86
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f131,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_3
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f2679,plain,
    ( spl8_86
    | spl8_21
    | ~ spl8_80 ),
    inference(avatar_split_clause,[],[f2678,f2267,f698,f2312])).

fof(f698,plain,
    ( spl8_21
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f2678,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | spl8_21
    | ~ spl8_80 ),
    inference(subsumption_resolution,[],[f2671,f700])).

fof(f700,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f698])).

fof(f2671,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl8_80 ),
    inference(resolution,[],[f2269,f259])).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_ordinal1(X0))
      | r2_hidden(X1,X0)
      | r2_hidden(X1,k1_tarski(X0)) ) ),
    inference(superposition,[],[f113,f74])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f2269,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK1))
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f2267])).

fof(f2368,plain,
    ( ~ spl8_23
    | ~ spl8_81 ),
    inference(avatar_split_clause,[],[f2352,f2271,f741])).

fof(f2352,plain,
    ( sK0 != sK1
    | ~ spl8_81 ),
    inference(superposition,[],[f76,f2273])).

fof(f76,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f2289,plain,
    ( ~ spl8_4
    | spl8_79 ),
    inference(avatar_contradiction_clause,[],[f2288])).

fof(f2288,plain,
    ( $false
    | ~ spl8_4
    | spl8_79 ),
    inference(subsumption_resolution,[],[f2285,f136])).

fof(f136,plain,
    ( v3_ordinal1(sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl8_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f2285,plain,
    ( ~ v3_ordinal1(sK1)
    | spl8_79 ),
    inference(resolution,[],[f2265,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f2265,plain,
    ( ~ v3_ordinal1(k1_ordinal1(sK1))
    | spl8_79 ),
    inference(avatar_component_clause,[],[f2263])).

fof(f2228,plain,(
    ~ spl8_10 ),
    inference(avatar_contradiction_clause,[],[f2210])).

fof(f2210,plain,
    ( $false
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f395,f117,f611,f203])).

fof(f203,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f112,f103])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f611,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_tarski(X0)) ),
    inference(duplicate_literal_removal,[],[f609])).

fof(f609,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_tarski(X0))
      | ~ r2_hidden(X0,k3_tarski(X0)) ) ),
    inference(resolution,[],[f221,f116])).

fof(f116,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK5(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f221,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK5(X5,X4))
      | ~ r2_hidden(X4,k3_tarski(X5)) ) ),
    inference(resolution,[],[f115,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f115,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f395,plain,
    ( r2_hidden(sK0,k3_tarski(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl8_10
  <=> r2_hidden(sK0,k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f2227,plain,
    ( ~ spl8_6
    | spl8_8
    | ~ spl8_9
    | spl8_11 ),
    inference(avatar_contradiction_clause,[],[f2209])).

fof(f2209,plain,
    ( $false
    | ~ spl8_6
    | spl8_8
    | ~ spl8_9
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f145,f381,f378,f398,f611,f97])).

fof(f398,plain,
    ( sK0 != k3_tarski(sK0)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f397])).

fof(f378,plain,
    ( ~ r2_hidden(k3_tarski(sK0),sK0)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f376])).

fof(f381,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl8_9
  <=> v3_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f701,plain,
    ( ~ spl8_21
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f689,f129,f698])).

fof(f689,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f131,f93])).

fof(f685,plain,
    ( spl8_19
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f680,f134,f682])).

fof(f680,plain,
    ( v1_ordinal1(sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f136,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f528,plain,
    ( spl8_1
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl8_1
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f525,f122])).

fof(f122,plain,
    ( ~ v4_ordinal1(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f525,plain,
    ( v4_ordinal1(sK0)
    | ~ spl8_11 ),
    inference(trivial_inequality_removal,[],[f517])).

fof(f517,plain,
    ( sK0 != sK0
    | v4_ordinal1(sK0)
    | ~ spl8_11 ),
    inference(superposition,[],[f99,f399])).

fof(f99,plain,(
    ! [X0] :
      ( k3_tarski(X0) != X0
      | v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f422,plain,
    ( ~ spl8_6
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | ~ spl8_6
    | spl8_9 ),
    inference(subsumption_resolution,[],[f418,f145])).

fof(f418,plain,
    ( ~ v3_ordinal1(sK0)
    | spl8_9 ),
    inference(resolution,[],[f382,f170])).

fof(f170,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f168,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK7(X0))
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK7(X0))
        & r2_hidden(sK7(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK7(X0))
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).

fof(f168,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | v3_ordinal1(sK7(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f95,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f95,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v3_ordinal1(k3_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f382,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f380])).

fof(f400,plain,
    ( ~ spl8_9
    | spl8_10
    | spl8_11
    | ~ spl8_6
    | spl8_8 ),
    inference(avatar_split_clause,[],[f391,f376,f143,f397,f393,f380])).

fof(f391,plain,
    ( sK0 = k3_tarski(sK0)
    | r2_hidden(sK0,k3_tarski(sK0))
    | ~ v3_ordinal1(k3_tarski(sK0))
    | ~ spl8_6
    | spl8_8 ),
    inference(subsumption_resolution,[],[f389,f145])).

fof(f389,plain,
    ( sK0 = k3_tarski(sK0)
    | r2_hidden(sK0,k3_tarski(sK0))
    | ~ v3_ordinal1(k3_tarski(sK0))
    | ~ v3_ordinal1(sK0)
    | spl8_8 ),
    inference(resolution,[],[f378,f97])).

fof(f383,plain,
    ( ~ spl8_8
    | ~ spl8_9
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f368,f139,f380,f376])).

fof(f139,plain,
    ( spl8_5
  <=> ! [X2] :
        ( r2_hidden(k1_ordinal1(X2),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f368,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    | ~ r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f352,f140])).

fof(f140,plain,
    ( ! [X2] :
        ( r2_hidden(k1_ordinal1(X2),sK0)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f352,plain,(
    ! [X11] : ~ r2_hidden(k1_ordinal1(k3_tarski(X11)),X11) ),
    inference(resolution,[],[f163,f75])).

fof(f75,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k3_tarski(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f92,f83])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f146,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f68,f143])).

fof(f68,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
        & r2_hidden(sK1,sK0)
        & v3_ordinal1(sK1) )
      | ~ v4_ordinal1(sK0) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK0)
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK0) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | v4_ordinal1(X0) )
        & v3_ordinal1(X0) )
   => ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),sK0)
            & r2_hidden(X1,sK0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK0)
            | ~ r2_hidden(X2,sK0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK0) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ~ r2_hidden(k1_ordinal1(X1),sK0)
        & r2_hidden(X1,sK0)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
      & r2_hidden(sK1,sK0)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f141,plain,
    ( spl8_1
    | spl8_5 ),
    inference(avatar_split_clause,[],[f69,f139,f120])).

fof(f69,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK0)
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f137,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f70,f134,f120])).

fof(f70,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f132,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f71,f129,f120])).

fof(f71,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f127,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f72,f124,f120])).

fof(f72,plain,
    ( ~ r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:06:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (32266)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (32280)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (32263)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (32269)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (32288)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (32264)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (32284)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (32281)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (32276)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (32273)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (32261)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (32259)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (32267)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (32262)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (32286)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (32287)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (32260)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (32265)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (32275)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (32278)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (32269)Refutation not found, incomplete strategy% (32269)------------------------------
% 0.21/0.55  % (32269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32269)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32269)Memory used [KB]: 10874
% 0.21/0.55  % (32269)Time elapsed: 0.130 s
% 0.21/0.55  % (32269)------------------------------
% 0.21/0.55  % (32269)------------------------------
% 0.21/0.55  % (32279)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (32270)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (32282)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (32268)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (32277)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (32274)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (32271)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (32283)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (32272)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.57  % (32285)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (32287)Refutation not found, incomplete strategy% (32287)------------------------------
% 0.21/0.57  % (32287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (32287)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (32287)Memory used [KB]: 10874
% 0.21/0.57  % (32287)Time elapsed: 0.158 s
% 0.21/0.57  % (32287)------------------------------
% 0.21/0.57  % (32287)------------------------------
% 0.21/0.57  % (32275)Refutation not found, incomplete strategy% (32275)------------------------------
% 0.21/0.57  % (32275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (32275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (32275)Memory used [KB]: 10746
% 0.21/0.58  % (32275)Time elapsed: 0.138 s
% 0.21/0.58  % (32275)------------------------------
% 0.21/0.58  % (32275)------------------------------
% 2.04/0.68  % (32314)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.04/0.71  % (32326)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.04/0.72  % (32330)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.20/0.83  % (32280)Refutation found. Thanks to Tanya!
% 3.20/0.83  % SZS status Theorem for theBenchmark
% 3.20/0.83  % SZS output start Proof for theBenchmark
% 3.20/0.83  fof(f4301,plain,(
% 3.20/0.83    $false),
% 3.20/0.83    inference(avatar_sat_refutation,[],[f127,f132,f137,f141,f146,f383,f400,f422,f528,f685,f701,f2227,f2228,f2289,f2368,f2679,f2697,f2708,f3922,f4043,f4300])).
% 3.20/0.83  fof(f4300,plain,(
% 3.20/0.83    ~spl8_1 | ~spl8_8),
% 3.20/0.83    inference(avatar_contradiction_clause,[],[f4299])).
% 3.20/0.83  fof(f4299,plain,(
% 3.20/0.83    $false | (~spl8_1 | ~spl8_8)),
% 3.20/0.83    inference(subsumption_resolution,[],[f4298,f121])).
% 3.20/0.83  fof(f121,plain,(
% 3.20/0.83    v4_ordinal1(sK0) | ~spl8_1),
% 3.20/0.83    inference(avatar_component_clause,[],[f120])).
% 3.20/0.83  fof(f120,plain,(
% 3.20/0.83    spl8_1 <=> v4_ordinal1(sK0)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.20/0.83  fof(f4298,plain,(
% 3.20/0.83    ~v4_ordinal1(sK0) | ~spl8_8),
% 3.20/0.83    inference(subsumption_resolution,[],[f4294,f154])).
% 3.20/0.83  fof(f154,plain,(
% 3.20/0.83    ( ! [X0] : (~r2_hidden(X0,X0)) )),
% 3.20/0.83    inference(resolution,[],[f83,f117])).
% 3.20/0.83  fof(f117,plain,(
% 3.20/0.83    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.20/0.83    inference(equality_resolution,[],[f101])).
% 3.20/0.83  fof(f101,plain,(
% 3.20/0.83    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.20/0.83    inference(cnf_transformation,[],[f67])).
% 3.20/0.83  fof(f67,plain,(
% 3.20/0.83    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/0.83    inference(flattening,[],[f66])).
% 3.20/0.83  fof(f66,plain,(
% 3.20/0.83    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/0.83    inference(nnf_transformation,[],[f4])).
% 3.20/0.83  fof(f4,axiom,(
% 3.20/0.83    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.20/0.83  fof(f83,plain,(
% 3.20/0.83    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f32])).
% 3.20/0.83  fof(f32,plain,(
% 3.20/0.83    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.20/0.83    inference(ennf_transformation,[],[f24])).
% 3.20/0.83  fof(f24,axiom,(
% 3.20/0.83    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 3.20/0.83  fof(f4294,plain,(
% 3.20/0.83    r2_hidden(sK0,sK0) | ~v4_ordinal1(sK0) | ~spl8_8),
% 3.20/0.83    inference(superposition,[],[f377,f98])).
% 3.20/0.83  fof(f98,plain,(
% 3.20/0.83    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f65])).
% 3.20/0.83  fof(f65,plain,(
% 3.20/0.83    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 3.20/0.83    inference(nnf_transformation,[],[f17])).
% 3.20/0.83  fof(f17,axiom,(
% 3.20/0.83    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_ordinal1)).
% 3.20/0.83  fof(f377,plain,(
% 3.20/0.83    r2_hidden(k3_tarski(sK0),sK0) | ~spl8_8),
% 3.20/0.83    inference(avatar_component_clause,[],[f376])).
% 3.20/0.83  fof(f376,plain,(
% 3.20/0.83    spl8_8 <=> r2_hidden(k3_tarski(sK0),sK0)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 3.20/0.83  fof(f4043,plain,(
% 3.20/0.83    ~spl8_19 | spl8_134),
% 3.20/0.83    inference(avatar_contradiction_clause,[],[f4042])).
% 3.20/0.83  fof(f4042,plain,(
% 3.20/0.83    $false | (~spl8_19 | spl8_134)),
% 3.20/0.83    inference(subsumption_resolution,[],[f4038,f684])).
% 3.20/0.83  fof(f684,plain,(
% 3.20/0.83    v1_ordinal1(sK1) | ~spl8_19),
% 3.20/0.83    inference(avatar_component_clause,[],[f682])).
% 3.20/0.83  fof(f682,plain,(
% 3.20/0.83    spl8_19 <=> v1_ordinal1(sK1)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 3.20/0.83  fof(f4038,plain,(
% 3.20/0.83    ~v1_ordinal1(sK1) | spl8_134),
% 3.20/0.83    inference(resolution,[],[f3921,f912])).
% 3.20/0.83  fof(f912,plain,(
% 3.20/0.83    ( ! [X0] : (r1_tarski(k3_tarski(X0),X0) | ~v1_ordinal1(X0)) )),
% 3.20/0.83    inference(duplicate_literal_removal,[],[f908])).
% 3.20/0.83  fof(f908,plain,(
% 3.20/0.83    ( ! [X0] : (r1_tarski(k3_tarski(X0),X0) | ~v1_ordinal1(X0) | r1_tarski(k3_tarski(X0),X0)) )),
% 3.20/0.83    inference(resolution,[],[f206,f91])).
% 3.20/0.83  fof(f91,plain,(
% 3.20/0.83    ( ! [X0,X1] : (~r1_tarski(sK6(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f62])).
% 3.20/0.83  fof(f62,plain,(
% 3.20/0.83    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 3.20/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f61])).
% 3.20/0.83  fof(f61,plain,(
% 3.20/0.83    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 3.20/0.83    introduced(choice_axiom,[])).
% 3.20/0.83  fof(f33,plain,(
% 3.20/0.83    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 3.20/0.83    inference(ennf_transformation,[],[f12])).
% 3.20/0.83  fof(f12,axiom,(
% 3.20/0.83    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 3.20/0.83  fof(f206,plain,(
% 3.20/0.83    ( ! [X0,X1] : (r1_tarski(sK6(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) | ~v1_ordinal1(X0)) )),
% 3.20/0.83    inference(resolution,[],[f90,f108])).
% 3.20/0.83  fof(f108,plain,(
% 3.20/0.83    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f42])).
% 3.20/0.83  fof(f42,plain,(
% 3.20/0.83    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 3.20/0.83    inference(ennf_transformation,[],[f27])).
% 3.20/0.83  fof(f27,plain,(
% 3.20/0.83    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.20/0.83    inference(unused_predicate_definition_removal,[],[f16])).
% 3.20/0.83  fof(f16,axiom,(
% 3.20/0.83    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 3.20/0.83  fof(f90,plain,(
% 3.20/0.83    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f62])).
% 3.20/0.83  fof(f3921,plain,(
% 3.20/0.83    ~r1_tarski(k3_tarski(sK1),sK1) | spl8_134),
% 3.20/0.83    inference(avatar_component_clause,[],[f3919])).
% 3.20/0.83  fof(f3919,plain,(
% 3.20/0.83    spl8_134 <=> r1_tarski(k3_tarski(sK1),sK1)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_134])])).
% 3.20/0.83  fof(f3922,plain,(
% 3.20/0.83    ~spl8_134 | ~spl8_11 | spl8_23 | ~spl8_81),
% 3.20/0.83    inference(avatar_split_clause,[],[f3917,f2271,f741,f397,f3919])).
% 3.20/0.83  fof(f397,plain,(
% 3.20/0.83    spl8_11 <=> sK0 = k3_tarski(sK0)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 3.20/0.83  fof(f741,plain,(
% 3.20/0.83    spl8_23 <=> sK0 = sK1),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 3.20/0.83  fof(f2271,plain,(
% 3.20/0.83    spl8_81 <=> sK0 = k1_ordinal1(sK1)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).
% 3.20/0.83  fof(f3917,plain,(
% 3.20/0.83    ~r1_tarski(k3_tarski(sK1),sK1) | (~spl8_11 | spl8_23 | ~spl8_81)),
% 3.20/0.83    inference(subsumption_resolution,[],[f3916,f742])).
% 3.20/0.83  fof(f742,plain,(
% 3.20/0.83    sK0 != sK1 | spl8_23),
% 3.20/0.83    inference(avatar_component_clause,[],[f741])).
% 3.20/0.83  fof(f3916,plain,(
% 3.20/0.83    sK0 = sK1 | ~r1_tarski(k3_tarski(sK1),sK1) | (~spl8_11 | ~spl8_81)),
% 3.20/0.83    inference(forward_demodulation,[],[f3880,f399])).
% 3.20/0.83  fof(f399,plain,(
% 3.20/0.83    sK0 = k3_tarski(sK0) | ~spl8_11),
% 3.20/0.83    inference(avatar_component_clause,[],[f397])).
% 3.20/0.83  fof(f3880,plain,(
% 3.20/0.83    sK1 = k3_tarski(sK0) | ~r1_tarski(k3_tarski(sK1),sK1) | ~spl8_81),
% 3.20/0.83    inference(superposition,[],[f1209,f2273])).
% 3.20/0.83  fof(f2273,plain,(
% 3.20/0.83    sK0 = k1_ordinal1(sK1) | ~spl8_81),
% 3.20/0.83    inference(avatar_component_clause,[],[f2271])).
% 3.20/0.83  fof(f1209,plain,(
% 3.20/0.83    ( ! [X0] : (k3_tarski(k1_ordinal1(X0)) = X0 | ~r1_tarski(k3_tarski(X0),X0)) )),
% 3.20/0.83    inference(forward_demodulation,[],[f1208,f106])).
% 3.20/0.83  fof(f106,plain,(
% 3.20/0.83    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 3.20/0.83    inference(cnf_transformation,[],[f11])).
% 3.20/0.83  fof(f11,axiom,(
% 3.20/0.83    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 3.20/0.83  fof(f1208,plain,(
% 3.20/0.83    ( ! [X0] : (k3_tarski(k1_ordinal1(X0)) = X0 | ~r1_tarski(k3_tarski(X0),k3_tarski(k1_tarski(X0)))) )),
% 3.20/0.83    inference(forward_demodulation,[],[f1174,f106])).
% 3.20/0.83  fof(f1174,plain,(
% 3.20/0.83    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = k3_tarski(k1_ordinal1(X0)) | ~r1_tarski(k3_tarski(X0),k3_tarski(k1_tarski(X0)))) )),
% 3.20/0.83    inference(superposition,[],[f235,f74])).
% 3.20/0.83  fof(f74,plain,(
% 3.20/0.83    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.20/0.83    inference(cnf_transformation,[],[f15])).
% 3.20/0.83  fof(f15,axiom,(
% 3.20/0.83    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 3.20/0.83  fof(f235,plain,(
% 3.20/0.83    ( ! [X2,X3] : (k3_tarski(X3) = k3_tarski(k2_xboole_0(X2,X3)) | ~r1_tarski(k3_tarski(X2),k3_tarski(X3))) )),
% 3.20/0.83    inference(superposition,[],[f104,f103])).
% 3.20/0.83  fof(f103,plain,(
% 3.20/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f41])).
% 3.20/0.83  fof(f41,plain,(
% 3.20/0.83    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.20/0.83    inference(ennf_transformation,[],[f5])).
% 3.20/0.83  fof(f5,axiom,(
% 3.20/0.83    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.20/0.83  fof(f104,plain,(
% 3.20/0.83    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 3.20/0.83    inference(cnf_transformation,[],[f13])).
% 3.20/0.83  fof(f13,axiom,(
% 3.20/0.83    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 3.20/0.83  fof(f2708,plain,(
% 3.20/0.83    spl8_81 | spl8_2 | ~spl8_6 | ~spl8_79 | spl8_80),
% 3.20/0.83    inference(avatar_split_clause,[],[f2707,f2267,f2263,f143,f124,f2271])).
% 3.20/0.83  fof(f124,plain,(
% 3.20/0.83    spl8_2 <=> r2_hidden(k1_ordinal1(sK1),sK0)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.20/0.83  fof(f143,plain,(
% 3.20/0.83    spl8_6 <=> v3_ordinal1(sK0)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 3.20/0.83  fof(f2263,plain,(
% 3.20/0.83    spl8_79 <=> v3_ordinal1(k1_ordinal1(sK1))),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).
% 3.20/0.83  fof(f2267,plain,(
% 3.20/0.83    spl8_80 <=> r2_hidden(sK0,k1_ordinal1(sK1))),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).
% 3.20/0.83  fof(f2707,plain,(
% 3.20/0.83    sK0 = k1_ordinal1(sK1) | (spl8_2 | ~spl8_6 | ~spl8_79 | spl8_80)),
% 3.20/0.83    inference(subsumption_resolution,[],[f2706,f2264])).
% 3.20/0.83  fof(f2264,plain,(
% 3.20/0.83    v3_ordinal1(k1_ordinal1(sK1)) | ~spl8_79),
% 3.20/0.83    inference(avatar_component_clause,[],[f2263])).
% 3.20/0.83  fof(f2706,plain,(
% 3.20/0.83    sK0 = k1_ordinal1(sK1) | ~v3_ordinal1(k1_ordinal1(sK1)) | (spl8_2 | ~spl8_6 | spl8_80)),
% 3.20/0.83    inference(subsumption_resolution,[],[f2705,f145])).
% 3.20/0.83  fof(f145,plain,(
% 3.20/0.83    v3_ordinal1(sK0) | ~spl8_6),
% 3.20/0.83    inference(avatar_component_clause,[],[f143])).
% 3.20/0.83  fof(f2705,plain,(
% 3.20/0.83    sK0 = k1_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k1_ordinal1(sK1)) | (spl8_2 | spl8_80)),
% 3.20/0.83    inference(subsumption_resolution,[],[f2703,f126])).
% 3.20/0.83  fof(f126,plain,(
% 3.20/0.83    ~r2_hidden(k1_ordinal1(sK1),sK0) | spl8_2),
% 3.20/0.83    inference(avatar_component_clause,[],[f124])).
% 3.20/0.83  fof(f2703,plain,(
% 3.20/0.83    sK0 = k1_ordinal1(sK1) | r2_hidden(k1_ordinal1(sK1),sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(k1_ordinal1(sK1)) | spl8_80),
% 3.20/0.83    inference(resolution,[],[f2268,f97])).
% 3.20/0.83  fof(f97,plain,(
% 3.20/0.83    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f40])).
% 3.20/0.83  fof(f40,plain,(
% 3.20/0.83    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.20/0.83    inference(flattening,[],[f39])).
% 3.20/0.83  fof(f39,plain,(
% 3.20/0.83    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.20/0.83    inference(ennf_transformation,[],[f21])).
% 3.20/0.83  fof(f21,axiom,(
% 3.20/0.83    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 3.20/0.83  fof(f2268,plain,(
% 3.20/0.83    ~r2_hidden(sK0,k1_ordinal1(sK1)) | spl8_80),
% 3.20/0.83    inference(avatar_component_clause,[],[f2267])).
% 3.20/0.83  fof(f2697,plain,(
% 3.20/0.83    ~spl8_3 | ~spl8_86),
% 3.20/0.83    inference(avatar_contradiction_clause,[],[f2686])).
% 3.20/0.83  fof(f2686,plain,(
% 3.20/0.83    $false | (~spl8_3 | ~spl8_86)),
% 3.20/0.83    inference(unit_resulting_resolution,[],[f131,f154,f2314,f252])).
% 3.20/0.83  fof(f252,plain,(
% 3.20/0.83    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_tarski(X0)) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 3.20/0.83    inference(superposition,[],[f114,f106])).
% 3.20/0.83  fof(f114,plain,(
% 3.20/0.83    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 3.20/0.83    inference(equality_resolution,[],[f86])).
% 3.20/0.83  fof(f86,plain,(
% 3.20/0.83    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 3.20/0.83    inference(cnf_transformation,[],[f60])).
% 3.20/0.83  fof(f60,plain,(
% 3.20/0.83    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & ((r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.20/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f56,f59,f58,f57])).
% 3.20/0.83  fof(f57,plain,(
% 3.20/0.83    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK3(X0,X1),X3)) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) | r2_hidden(sK3(X0,X1),X1))))),
% 3.20/0.83    introduced(choice_axiom,[])).
% 3.20/0.83  fof(f58,plain,(
% 3.20/0.83    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK3(X0,X1),X4)) => (r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),sK4(X0,X1))))),
% 3.20/0.83    introduced(choice_axiom,[])).
% 3.20/0.83  fof(f59,plain,(
% 3.20/0.83    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK5(X0,X5),X0) & r2_hidden(X5,sK5(X0,X5))))),
% 3.20/0.83    introduced(choice_axiom,[])).
% 3.20/0.83  fof(f56,plain,(
% 3.20/0.83    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.20/0.83    inference(rectify,[],[f55])).
% 3.20/0.83  fof(f55,plain,(
% 3.20/0.83    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.20/0.83    inference(nnf_transformation,[],[f9])).
% 3.20/0.83  fof(f9,axiom,(
% 3.20/0.83    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 3.20/0.83  fof(f2314,plain,(
% 3.20/0.83    r2_hidden(sK0,k1_tarski(sK1)) | ~spl8_86),
% 3.20/0.83    inference(avatar_component_clause,[],[f2312])).
% 3.20/0.83  fof(f2312,plain,(
% 3.20/0.83    spl8_86 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).
% 3.20/0.83  fof(f131,plain,(
% 3.20/0.83    r2_hidden(sK1,sK0) | ~spl8_3),
% 3.20/0.83    inference(avatar_component_clause,[],[f129])).
% 3.20/0.83  fof(f129,plain,(
% 3.20/0.83    spl8_3 <=> r2_hidden(sK1,sK0)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 3.20/0.83  fof(f2679,plain,(
% 3.20/0.83    spl8_86 | spl8_21 | ~spl8_80),
% 3.20/0.83    inference(avatar_split_clause,[],[f2678,f2267,f698,f2312])).
% 3.20/0.83  fof(f698,plain,(
% 3.20/0.83    spl8_21 <=> r2_hidden(sK0,sK1)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 3.20/0.83  fof(f2678,plain,(
% 3.20/0.83    r2_hidden(sK0,k1_tarski(sK1)) | (spl8_21 | ~spl8_80)),
% 3.20/0.83    inference(subsumption_resolution,[],[f2671,f700])).
% 3.20/0.83  fof(f700,plain,(
% 3.20/0.83    ~r2_hidden(sK0,sK1) | spl8_21),
% 3.20/0.83    inference(avatar_component_clause,[],[f698])).
% 3.20/0.83  fof(f2671,plain,(
% 3.20/0.83    r2_hidden(sK0,sK1) | r2_hidden(sK0,k1_tarski(sK1)) | ~spl8_80),
% 3.20/0.83    inference(resolution,[],[f2269,f259])).
% 3.20/0.83  fof(f259,plain,(
% 3.20/0.83    ( ! [X0,X1] : (~r2_hidden(X1,k1_ordinal1(X0)) | r2_hidden(X1,X0) | r2_hidden(X1,k1_tarski(X0))) )),
% 3.20/0.83    inference(superposition,[],[f113,f74])).
% 3.20/0.83  fof(f113,plain,(
% 3.20/0.83    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 3.20/0.83    inference(equality_resolution,[],[f77])).
% 3.20/0.83  fof(f77,plain,(
% 3.20/0.83    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.20/0.83    inference(cnf_transformation,[],[f54])).
% 3.20/0.83  fof(f54,plain,(
% 3.20/0.83    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.20/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).
% 3.20/0.83  fof(f53,plain,(
% 3.20/0.83    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.20/0.83    introduced(choice_axiom,[])).
% 3.20/0.83  fof(f52,plain,(
% 3.20/0.83    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.20/0.83    inference(rectify,[],[f51])).
% 3.20/0.83  fof(f51,plain,(
% 3.20/0.83    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.20/0.83    inference(flattening,[],[f50])).
% 3.20/0.83  fof(f50,plain,(
% 3.20/0.83    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.20/0.83    inference(nnf_transformation,[],[f3])).
% 3.20/0.83  fof(f3,axiom,(
% 3.20/0.83    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 3.20/0.83  fof(f2269,plain,(
% 3.20/0.83    r2_hidden(sK0,k1_ordinal1(sK1)) | ~spl8_80),
% 3.20/0.83    inference(avatar_component_clause,[],[f2267])).
% 3.20/0.83  fof(f2368,plain,(
% 3.20/0.83    ~spl8_23 | ~spl8_81),
% 3.20/0.83    inference(avatar_split_clause,[],[f2352,f2271,f741])).
% 3.20/0.83  fof(f2352,plain,(
% 3.20/0.83    sK0 != sK1 | ~spl8_81),
% 3.20/0.83    inference(superposition,[],[f76,f2273])).
% 3.20/0.83  fof(f76,plain,(
% 3.20/0.83    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 3.20/0.83    inference(cnf_transformation,[],[f19])).
% 3.20/0.83  fof(f19,axiom,(
% 3.20/0.83    ! [X0] : k1_ordinal1(X0) != X0),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
% 3.20/0.83  fof(f2289,plain,(
% 3.20/0.83    ~spl8_4 | spl8_79),
% 3.20/0.83    inference(avatar_contradiction_clause,[],[f2288])).
% 3.20/0.83  fof(f2288,plain,(
% 3.20/0.83    $false | (~spl8_4 | spl8_79)),
% 3.20/0.83    inference(subsumption_resolution,[],[f2285,f136])).
% 3.20/0.83  fof(f136,plain,(
% 3.20/0.83    v3_ordinal1(sK1) | ~spl8_4),
% 3.20/0.83    inference(avatar_component_clause,[],[f134])).
% 3.20/0.83  fof(f134,plain,(
% 3.20/0.83    spl8_4 <=> v3_ordinal1(sK1)),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 3.20/0.83  fof(f2285,plain,(
% 3.20/0.83    ~v3_ordinal1(sK1) | spl8_79),
% 3.20/0.83    inference(resolution,[],[f2265,f73])).
% 3.20/0.83  fof(f73,plain,(
% 3.20/0.83    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f31])).
% 3.20/0.83  fof(f31,plain,(
% 3.20/0.83    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.20/0.83    inference(ennf_transformation,[],[f22])).
% 3.20/0.83  fof(f22,axiom,(
% 3.20/0.83    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 3.20/0.83  fof(f2265,plain,(
% 3.20/0.83    ~v3_ordinal1(k1_ordinal1(sK1)) | spl8_79),
% 3.20/0.83    inference(avatar_component_clause,[],[f2263])).
% 3.20/0.83  fof(f2228,plain,(
% 3.20/0.83    ~spl8_10),
% 3.20/0.83    inference(avatar_contradiction_clause,[],[f2210])).
% 3.20/0.83  fof(f2210,plain,(
% 3.20/0.83    $false | ~spl8_10),
% 3.20/0.83    inference(unit_resulting_resolution,[],[f395,f117,f611,f203])).
% 3.20/0.83  fof(f203,plain,(
% 3.20/0.83    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X4,X2) | r2_hidden(X4,X3)) )),
% 3.20/0.83    inference(superposition,[],[f112,f103])).
% 3.20/0.83  fof(f112,plain,(
% 3.20/0.83    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.20/0.83    inference(equality_resolution,[],[f78])).
% 3.20/0.83  fof(f78,plain,(
% 3.20/0.83    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.20/0.83    inference(cnf_transformation,[],[f54])).
% 3.20/0.83  fof(f611,plain,(
% 3.20/0.83    ( ! [X0] : (~r2_hidden(X0,k3_tarski(X0))) )),
% 3.20/0.83    inference(duplicate_literal_removal,[],[f609])).
% 3.20/0.83  fof(f609,plain,(
% 3.20/0.83    ( ! [X0] : (~r2_hidden(X0,k3_tarski(X0)) | ~r2_hidden(X0,k3_tarski(X0))) )),
% 3.20/0.83    inference(resolution,[],[f221,f116])).
% 3.20/0.83  fof(f116,plain,(
% 3.20/0.83    ( ! [X0,X5] : (r2_hidden(X5,sK5(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.20/0.83    inference(equality_resolution,[],[f84])).
% 3.20/0.83  fof(f84,plain,(
% 3.20/0.83    ( ! [X0,X5,X1] : (r2_hidden(X5,sK5(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.20/0.83    inference(cnf_transformation,[],[f60])).
% 3.20/0.83  fof(f221,plain,(
% 3.20/0.83    ( ! [X4,X5] : (~r2_hidden(X5,sK5(X5,X4)) | ~r2_hidden(X4,k3_tarski(X5))) )),
% 3.20/0.83    inference(resolution,[],[f115,f93])).
% 3.20/0.83  fof(f93,plain,(
% 3.20/0.83    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f35])).
% 3.20/0.83  fof(f35,plain,(
% 3.20/0.83    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.20/0.83    inference(ennf_transformation,[],[f1])).
% 3.20/0.83  fof(f1,axiom,(
% 3.20/0.83    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 3.20/0.83  fof(f115,plain,(
% 3.20/0.83    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.20/0.83    inference(equality_resolution,[],[f85])).
% 3.20/0.83  fof(f85,plain,(
% 3.20/0.83    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.20/0.83    inference(cnf_transformation,[],[f60])).
% 3.20/0.83  fof(f395,plain,(
% 3.20/0.83    r2_hidden(sK0,k3_tarski(sK0)) | ~spl8_10),
% 3.20/0.83    inference(avatar_component_clause,[],[f393])).
% 3.20/0.83  fof(f393,plain,(
% 3.20/0.83    spl8_10 <=> r2_hidden(sK0,k3_tarski(sK0))),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 3.20/0.83  fof(f2227,plain,(
% 3.20/0.83    ~spl8_6 | spl8_8 | ~spl8_9 | spl8_11),
% 3.20/0.83    inference(avatar_contradiction_clause,[],[f2209])).
% 3.20/0.83  fof(f2209,plain,(
% 3.20/0.83    $false | (~spl8_6 | spl8_8 | ~spl8_9 | spl8_11)),
% 3.20/0.83    inference(unit_resulting_resolution,[],[f145,f381,f378,f398,f611,f97])).
% 3.20/0.83  fof(f398,plain,(
% 3.20/0.83    sK0 != k3_tarski(sK0) | spl8_11),
% 3.20/0.83    inference(avatar_component_clause,[],[f397])).
% 3.20/0.83  fof(f378,plain,(
% 3.20/0.83    ~r2_hidden(k3_tarski(sK0),sK0) | spl8_8),
% 3.20/0.83    inference(avatar_component_clause,[],[f376])).
% 3.20/0.83  fof(f381,plain,(
% 3.20/0.83    v3_ordinal1(k3_tarski(sK0)) | ~spl8_9),
% 3.20/0.83    inference(avatar_component_clause,[],[f380])).
% 3.20/0.83  fof(f380,plain,(
% 3.20/0.83    spl8_9 <=> v3_ordinal1(k3_tarski(sK0))),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 3.20/0.83  fof(f701,plain,(
% 3.20/0.83    ~spl8_21 | ~spl8_3),
% 3.20/0.83    inference(avatar_split_clause,[],[f689,f129,f698])).
% 3.20/0.83  fof(f689,plain,(
% 3.20/0.83    ~r2_hidden(sK0,sK1) | ~spl8_3),
% 3.20/0.83    inference(resolution,[],[f131,f93])).
% 3.20/0.83  fof(f685,plain,(
% 3.20/0.83    spl8_19 | ~spl8_4),
% 3.20/0.83    inference(avatar_split_clause,[],[f680,f134,f682])).
% 3.20/0.83  fof(f680,plain,(
% 3.20/0.83    v1_ordinal1(sK1) | ~spl8_4),
% 3.20/0.83    inference(resolution,[],[f136,f110])).
% 3.20/0.83  fof(f110,plain,(
% 3.20/0.83    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f43])).
% 3.20/0.83  fof(f43,plain,(
% 3.20/0.83    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.20/0.83    inference(ennf_transformation,[],[f28])).
% 3.20/0.83  fof(f28,plain,(
% 3.20/0.83    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.20/0.83    inference(pure_predicate_removal,[],[f14])).
% 3.20/0.83  fof(f14,axiom,(
% 3.20/0.83    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 3.20/0.83  fof(f528,plain,(
% 3.20/0.83    spl8_1 | ~spl8_11),
% 3.20/0.83    inference(avatar_contradiction_clause,[],[f527])).
% 3.20/0.83  fof(f527,plain,(
% 3.20/0.83    $false | (spl8_1 | ~spl8_11)),
% 3.20/0.83    inference(subsumption_resolution,[],[f525,f122])).
% 3.20/0.83  fof(f122,plain,(
% 3.20/0.83    ~v4_ordinal1(sK0) | spl8_1),
% 3.20/0.83    inference(avatar_component_clause,[],[f120])).
% 3.20/0.83  fof(f525,plain,(
% 3.20/0.83    v4_ordinal1(sK0) | ~spl8_11),
% 3.20/0.83    inference(trivial_inequality_removal,[],[f517])).
% 3.20/0.83  fof(f517,plain,(
% 3.20/0.83    sK0 != sK0 | v4_ordinal1(sK0) | ~spl8_11),
% 3.20/0.83    inference(superposition,[],[f99,f399])).
% 3.20/0.83  fof(f99,plain,(
% 3.20/0.83    ( ! [X0] : (k3_tarski(X0) != X0 | v4_ordinal1(X0)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f65])).
% 3.20/0.83  fof(f422,plain,(
% 3.20/0.83    ~spl8_6 | spl8_9),
% 3.20/0.83    inference(avatar_contradiction_clause,[],[f421])).
% 3.20/0.83  fof(f421,plain,(
% 3.20/0.83    $false | (~spl8_6 | spl8_9)),
% 3.20/0.83    inference(subsumption_resolution,[],[f418,f145])).
% 3.20/0.83  fof(f418,plain,(
% 3.20/0.83    ~v3_ordinal1(sK0) | spl8_9),
% 3.20/0.83    inference(resolution,[],[f382,f170])).
% 3.20/0.83  fof(f170,plain,(
% 3.20/0.83    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(X0)) )),
% 3.20/0.83    inference(subsumption_resolution,[],[f168,f96])).
% 3.20/0.83  fof(f96,plain,(
% 3.20/0.83    ( ! [X0] : (~v3_ordinal1(sK7(X0)) | v3_ordinal1(k3_tarski(X0))) )),
% 3.20/0.83    inference(cnf_transformation,[],[f64])).
% 3.20/0.83  fof(f64,plain,(
% 3.20/0.83    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK7(X0)) & r2_hidden(sK7(X0),X0)))),
% 3.20/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f63])).
% 3.20/0.83  fof(f63,plain,(
% 3.20/0.83    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK7(X0)) & r2_hidden(sK7(X0),X0)))),
% 3.20/0.83    introduced(choice_axiom,[])).
% 3.20/0.83  fof(f38,plain,(
% 3.20/0.83    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 3.20/0.83    inference(ennf_transformation,[],[f23])).
% 3.20/0.83  fof(f23,axiom,(
% 3.20/0.83    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_ordinal1)).
% 3.20/0.83  fof(f168,plain,(
% 3.20/0.83    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | v3_ordinal1(sK7(X0)) | ~v3_ordinal1(X0)) )),
% 3.20/0.83    inference(resolution,[],[f95,f94])).
% 3.20/0.83  fof(f94,plain,(
% 3.20/0.83    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f37])).
% 3.20/0.83  fof(f37,plain,(
% 3.20/0.83    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 3.20/0.83    inference(flattening,[],[f36])).
% 3.20/0.83  fof(f36,plain,(
% 3.20/0.83    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 3.20/0.83    inference(ennf_transformation,[],[f20])).
% 3.20/0.83  fof(f20,axiom,(
% 3.20/0.83    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).
% 3.20/0.83  fof(f95,plain,(
% 3.20/0.83    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v3_ordinal1(k3_tarski(X0))) )),
% 3.20/0.83    inference(cnf_transformation,[],[f64])).
% 3.20/0.83  fof(f382,plain,(
% 3.20/0.83    ~v3_ordinal1(k3_tarski(sK0)) | spl8_9),
% 3.20/0.83    inference(avatar_component_clause,[],[f380])).
% 3.20/0.83  fof(f400,plain,(
% 3.20/0.83    ~spl8_9 | spl8_10 | spl8_11 | ~spl8_6 | spl8_8),
% 3.20/0.83    inference(avatar_split_clause,[],[f391,f376,f143,f397,f393,f380])).
% 3.20/0.83  fof(f391,plain,(
% 3.20/0.83    sK0 = k3_tarski(sK0) | r2_hidden(sK0,k3_tarski(sK0)) | ~v3_ordinal1(k3_tarski(sK0)) | (~spl8_6 | spl8_8)),
% 3.20/0.83    inference(subsumption_resolution,[],[f389,f145])).
% 3.20/0.83  fof(f389,plain,(
% 3.20/0.83    sK0 = k3_tarski(sK0) | r2_hidden(sK0,k3_tarski(sK0)) | ~v3_ordinal1(k3_tarski(sK0)) | ~v3_ordinal1(sK0) | spl8_8),
% 3.20/0.83    inference(resolution,[],[f378,f97])).
% 3.20/0.83  fof(f383,plain,(
% 3.20/0.83    ~spl8_8 | ~spl8_9 | ~spl8_5),
% 3.20/0.83    inference(avatar_split_clause,[],[f368,f139,f380,f376])).
% 3.20/0.83  fof(f139,plain,(
% 3.20/0.83    spl8_5 <=> ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0))),
% 3.20/0.83    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 3.20/0.83  fof(f368,plain,(
% 3.20/0.83    ~v3_ordinal1(k3_tarski(sK0)) | ~r2_hidden(k3_tarski(sK0),sK0) | ~spl8_5),
% 3.20/0.83    inference(resolution,[],[f352,f140])).
% 3.20/0.83  fof(f140,plain,(
% 3.20/0.83    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~v3_ordinal1(X2) | ~r2_hidden(X2,sK0)) ) | ~spl8_5),
% 3.20/0.83    inference(avatar_component_clause,[],[f139])).
% 3.20/0.83  fof(f352,plain,(
% 3.20/0.83    ( ! [X11] : (~r2_hidden(k1_ordinal1(k3_tarski(X11)),X11)) )),
% 3.20/0.83    inference(resolution,[],[f163,f75])).
% 3.20/0.83  fof(f75,plain,(
% 3.20/0.83    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.20/0.83    inference(cnf_transformation,[],[f18])).
% 3.20/0.83  fof(f18,axiom,(
% 3.20/0.83    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 3.20/0.83  fof(f163,plain,(
% 3.20/0.83    ( ! [X0,X1] : (~r2_hidden(k3_tarski(X1),X0) | ~r2_hidden(X0,X1)) )),
% 3.20/0.83    inference(resolution,[],[f92,f83])).
% 3.20/0.83  fof(f92,plain,(
% 3.20/0.83    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f34])).
% 3.20/0.83  fof(f34,plain,(
% 3.20/0.83    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 3.20/0.83    inference(ennf_transformation,[],[f10])).
% 3.20/0.83  fof(f10,axiom,(
% 3.20/0.83    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 3.20/0.83  fof(f146,plain,(
% 3.20/0.83    spl8_6),
% 3.20/0.83    inference(avatar_split_clause,[],[f68,f143])).
% 3.20/0.83  fof(f68,plain,(
% 3.20/0.83    v3_ordinal1(sK0)),
% 3.20/0.83    inference(cnf_transformation,[],[f49])).
% 3.20/0.83  fof(f49,plain,(
% 3.20/0.83    ((~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0)),
% 3.20/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).
% 3.20/0.83  fof(f47,plain,(
% 3.20/0.83    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) | ~v4_ordinal1(sK0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) | v4_ordinal1(sK0)) & v3_ordinal1(sK0))),
% 3.20/0.83    introduced(choice_axiom,[])).
% 3.20/0.83  fof(f48,plain,(
% 3.20/0.83    ? [X1] : (~r2_hidden(k1_ordinal1(X1),sK0) & r2_hidden(X1,sK0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK1),sK0) & r2_hidden(sK1,sK0) & v3_ordinal1(sK1))),
% 3.20/0.83    introduced(choice_axiom,[])).
% 3.20/0.83  fof(f46,plain,(
% 3.20/0.83    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.20/0.83    inference(rectify,[],[f45])).
% 3.20/0.83  fof(f45,plain,(
% 3.20/0.83    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 3.20/0.83    inference(flattening,[],[f44])).
% 3.20/0.83  fof(f44,plain,(
% 3.20/0.83    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 3.20/0.83    inference(nnf_transformation,[],[f30])).
% 3.20/0.83  fof(f30,plain,(
% 3.20/0.83    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.20/0.83    inference(flattening,[],[f29])).
% 3.20/0.83  fof(f29,plain,(
% 3.20/0.83    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 3.20/0.83    inference(ennf_transformation,[],[f26])).
% 3.20/0.83  fof(f26,negated_conjecture,(
% 3.20/0.83    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.20/0.83    inference(negated_conjecture,[],[f25])).
% 3.20/0.83  fof(f25,conjecture,(
% 3.20/0.83    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.20/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 3.20/0.83  fof(f141,plain,(
% 3.20/0.83    spl8_1 | spl8_5),
% 3.20/0.83    inference(avatar_split_clause,[],[f69,f139,f120])).
% 3.20/0.83  fof(f69,plain,(
% 3.20/0.83    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK0) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v4_ordinal1(sK0)) )),
% 3.20/0.83    inference(cnf_transformation,[],[f49])).
% 3.20/0.83  fof(f137,plain,(
% 3.20/0.83    ~spl8_1 | spl8_4),
% 3.20/0.83    inference(avatar_split_clause,[],[f70,f134,f120])).
% 3.20/0.83  fof(f70,plain,(
% 3.20/0.83    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 3.20/0.83    inference(cnf_transformation,[],[f49])).
% 3.20/0.83  fof(f132,plain,(
% 3.20/0.83    ~spl8_1 | spl8_3),
% 3.20/0.83    inference(avatar_split_clause,[],[f71,f129,f120])).
% 3.20/0.83  fof(f71,plain,(
% 3.20/0.83    r2_hidden(sK1,sK0) | ~v4_ordinal1(sK0)),
% 3.20/0.83    inference(cnf_transformation,[],[f49])).
% 3.20/0.83  fof(f127,plain,(
% 3.20/0.83    ~spl8_1 | ~spl8_2),
% 3.20/0.83    inference(avatar_split_clause,[],[f72,f124,f120])).
% 3.20/0.83  fof(f72,plain,(
% 3.20/0.83    ~r2_hidden(k1_ordinal1(sK1),sK0) | ~v4_ordinal1(sK0)),
% 3.20/0.83    inference(cnf_transformation,[],[f49])).
% 3.20/0.83  % SZS output end Proof for theBenchmark
% 3.20/0.83  % (32280)------------------------------
% 3.20/0.83  % (32280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.83  % (32280)Termination reason: Refutation
% 3.20/0.83  
% 3.20/0.83  % (32280)Memory used [KB]: 8827
% 3.20/0.83  % (32280)Time elapsed: 0.400 s
% 3.20/0.83  % (32280)------------------------------
% 3.20/0.83  % (32280)------------------------------
% 3.20/0.84  % (32258)Success in time 0.468 s
%------------------------------------------------------------------------------
