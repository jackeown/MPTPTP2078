%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t84_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:34 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 173 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :    7
%              Number of atoms          :  191 ( 377 expanded)
%              Number of equality atoms :   36 (  77 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f57,f64,f71,f81,f90,f101,f112,f122,f145,f152,f174,f185,f221,f237,f249,f350,f354])).

fof(f354,plain,
    ( ~ spl3_18
    | spl3_23
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | ~ spl3_18
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f344,f173])).

fof(f173,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_23
  <=> k3_xboole_0(sK0,sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f344,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl3_18
    | ~ spl3_28 ),
    inference(superposition,[],[f236,f205])).

fof(f205,plain,
    ( ! [X12] : k3_xboole_0(sK0,X12) = k3_xboole_0(sK0,k4_xboole_0(X12,sK2))
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f197,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t84_xboole_1.p',t3_boole)).

fof(f197,plain,
    ( ! [X12] : k4_xboole_0(k3_xboole_0(sK0,X12),k1_xboole_0) = k3_xboole_0(sK0,k4_xboole_0(X12,sK2))
    | ~ spl3_18 ),
    inference(superposition,[],[f43,f144])).

fof(f144,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_18
  <=> k3_xboole_0(sK0,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t84_xboole_1.p',t50_xboole_1)).

fof(f236,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl3_28
  <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f350,plain,
    ( ~ spl3_18
    | spl3_23
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f349])).

fof(f349,plain,
    ( $false
    | ~ spl3_18
    | ~ spl3_23
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f341,f173])).

fof(f341,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl3_18
    | ~ spl3_28 ),
    inference(superposition,[],[f205,f236])).

fof(f249,plain,
    ( spl3_30
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f133,f120,f247])).

fof(f247,plain,
    ( spl3_30
  <=> k3_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f120,plain,
    ( spl3_16
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f133,plain,
    ( k3_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k1_xboole_0
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f121,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t84_xboole_1.p',d7_xboole_0)).

fof(f121,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f120])).

fof(f237,plain,
    ( spl3_28
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f131,f69,f235])).

fof(f69,plain,
    ( spl3_6
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f131,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f70,f40])).

fof(f70,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f221,plain,
    ( ~ spl3_27
    | spl3_15 ),
    inference(avatar_split_clause,[],[f154,f110,f219])).

fof(f219,plain,
    ( spl3_27
  <=> k3_xboole_0(sK1,sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f110,plain,
    ( spl3_15
  <=> ~ r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f154,plain,
    ( k3_xboole_0(sK1,sK0) != k1_xboole_0
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f111,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f185,plain,
    ( ~ spl3_25
    | ~ spl3_8
    | spl3_23 ),
    inference(avatar_split_clause,[],[f178,f172,f79,f183])).

fof(f183,plain,
    ( spl3_25
  <=> ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f79,plain,
    ( spl3_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f178,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f80,f173,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t84_xboole_1.p',t8_boole)).

fof(f80,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f174,plain,
    ( ~ spl3_23
    | spl3_3 ),
    inference(avatar_split_clause,[],[f153,f55,f172])).

fof(f55,plain,
    ( spl3_3
  <=> ~ r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f153,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f56,f41])).

fof(f56,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f152,plain,
    ( spl3_20
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f132,f99,f150])).

fof(f150,plain,
    ( spl3_20
  <=> k3_xboole_0(sK2,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f99,plain,
    ( spl3_12
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f132,plain,
    ( k3_xboole_0(sK2,sK0) = k1_xboole_0
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f100,f40])).

fof(f100,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f145,plain,
    ( spl3_18
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f130,f62,f143])).

fof(f62,plain,
    ( spl3_4
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f130,plain,
    ( k3_xboole_0(sK0,sK2) = k1_xboole_0
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f63,f40])).

fof(f63,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f122,plain,
    ( spl3_16
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f92,f69,f120])).

fof(f92,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f70,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t84_xboole_1.p',symmetry_r1_xboole_0)).

fof(f112,plain,
    ( ~ spl3_15
    | spl3_3 ),
    inference(avatar_split_clause,[],[f93,f55,f110])).

fof(f93,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f56,f39])).

fof(f101,plain,
    ( spl3_12
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f91,f62,f99])).

fof(f91,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f63,f39])).

fof(f90,plain,
    ( spl3_10
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f72,f48,f88])).

fof(f88,plain,
    ( spl3_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f48,plain,
    ( spl3_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f72,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t84_xboole_1.p',t6_boole)).

fof(f49,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f48])).

fof(f81,plain,
    ( spl3_8
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f74,f48,f79])).

fof(f74,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_0 ),
    inference(backward_demodulation,[],[f72,f49])).

fof(f71,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
          & r1_xboole_0(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t84_xboole_1.p',t84_xboole_1)).

fof(f64,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f32,f48])).

fof(f32,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t84_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
