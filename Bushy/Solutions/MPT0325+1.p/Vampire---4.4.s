%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t138_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:01 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 625 expanded)
%              Number of leaves         :   34 ( 235 expanded)
%              Depth                    :   12
%              Number of atoms          :  514 (1265 expanded)
%              Number of equality atoms :  205 ( 672 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f624,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f55,f68,f98,f171,f218,f221,f223,f226,f292,f296,f313,f328,f396,f400,f417,f435,f438,f463,f472,f475,f480,f482,f490,f508,f518,f521,f524,f526,f534,f544,f574,f583,f584,f591,f614,f623])).

fof(f623,plain,
    ( spl4_5
    | ~ spl4_38 ),
    inference(avatar_contradiction_clause,[],[f622])).

fof(f622,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_38 ),
    inference(subsumption_resolution,[],[f617,f61])).

fof(f61,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_5
  <=> ~ r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f617,plain,
    ( r1_tarski(sK1,sK3)
    | ~ spl4_38 ),
    inference(superposition,[],[f74,f613])).

fof(f613,plain,
    ( k3_xboole_0(sK1,sK3) = sK1
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f612])).

fof(f612,plain,
    ( spl4_38
  <=> k3_xboole_0(sK1,sK3) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f74,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t138_zfmisc_1.p',commutativity_k3_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t138_zfmisc_1.p',t17_xboole_1)).

fof(f614,plain,
    ( spl4_38
    | ~ spl4_14
    | spl4_17
    | ~ spl4_20
    | spl4_31 ),
    inference(avatar_split_clause,[],[f607,f500,f394,f305,f290,f612])).

fof(f290,plain,
    ( spl4_14
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f305,plain,
    ( spl4_17
  <=> k1_xboole_0 != k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f394,plain,
    ( spl4_20
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f500,plain,
    ( spl4_31
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f607,plain,
    ( k3_xboole_0(sK1,sK3) = sK1
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_20
    | ~ spl4_31 ),
    inference(trivial_inequality_removal,[],[f605])).

fof(f605,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1)
    | k3_xboole_0(sK1,sK3) = sK1
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_20
    | ~ spl4_31 ),
    inference(superposition,[],[f559,f291])).

fof(f291,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f290])).

fof(f559,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X6,X7)
        | sK1 = X7 )
    | ~ spl4_17
    | ~ spl4_20
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f558,f501])).

fof(f501,plain,
    ( k1_xboole_0 != sK1
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f500])).

fof(f558,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X6,X7)
        | k1_xboole_0 = sK1
        | sK1 = X7 )
    | ~ spl4_17
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f549,f306])).

fof(f306,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f305])).

fof(f549,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X6,X7)
        | k1_xboole_0 = k3_xboole_0(sK0,sK2)
        | k1_xboole_0 = sK1
        | sK1 = X7 )
    | ~ spl4_20 ),
    inference(superposition,[],[f33,f395])).

fof(f395,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f394])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t138_zfmisc_1.p',t134_zfmisc_1)).

fof(f591,plain,
    ( spl4_36
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f581,f572,f589])).

fof(f589,plain,
    ( spl4_36
  <=> k3_xboole_0(sK2,sK0) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f572,plain,
    ( spl4_34
  <=> k3_xboole_0(sK0,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f581,plain,
    ( k3_xboole_0(sK2,sK0) = sK0
    | ~ spl4_34 ),
    inference(superposition,[],[f125,f573])).

fof(f573,plain,
    ( k3_xboole_0(sK0,sK2) = sK0
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f572])).

fof(f125,plain,(
    ! [X4,X5] : k3_xboole_0(X4,X5) = k3_xboole_0(X5,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f103,f38])).

fof(f103,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k3_xboole_0(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f90,f38])).

fof(f90,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(resolution,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t138_zfmisc_1.p',t28_xboole_1)).

fof(f584,plain,
    ( spl4_6
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f577,f572,f63])).

fof(f63,plain,
    ( spl4_6
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f577,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_34 ),
    inference(superposition,[],[f74,f573])).

fof(f583,plain,
    ( spl4_7
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f582])).

fof(f582,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f577,f67])).

fof(f67,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_7
  <=> ~ r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f574,plain,
    ( spl4_34
    | ~ spl4_20
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f567,f461,f394,f572])).

fof(f461,plain,
    ( spl4_28
  <=> ! [X7,X6] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X6,X7)
        | sK0 = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f567,plain,
    ( k3_xboole_0(sK0,sK2) = sK0
    | ~ spl4_20
    | ~ spl4_28 ),
    inference(trivial_inequality_removal,[],[f564])).

fof(f564,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(sK0,sK1)
    | k3_xboole_0(sK0,sK2) = sK0
    | ~ spl4_20
    | ~ spl4_28 ),
    inference(superposition,[],[f462,f395])).

fof(f462,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X6,X7)
        | sK0 = X6 )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f461])).

fof(f544,plain,
    ( spl4_32
    | spl4_17
    | ~ spl4_20
    | spl4_31 ),
    inference(avatar_split_clause,[],[f543,f500,f394,f305,f506])).

fof(f506,plain,
    ( spl4_32
  <=> ! [X3,X2] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k3_xboole_0(sK0,sK2) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f543,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k3_xboole_0(sK0,sK2) = X2 )
    | ~ spl4_17
    | ~ spl4_20
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f542,f501])).

fof(f542,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = sK1
        | k3_xboole_0(sK0,sK2) = X2 )
    | ~ spl4_17
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f538,f306])).

fof(f538,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = k3_xboole_0(sK0,sK2)
        | k1_xboole_0 = sK1
        | k3_xboole_0(sK0,sK2) = X2 )
    | ~ spl4_20 ),
    inference(superposition,[],[f32,f395])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(X2,X3)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f534,plain,
    ( spl4_28
    | ~ spl4_14
    | spl4_23
    | spl4_27 ),
    inference(avatar_split_clause,[],[f533,f455,f409,f290,f461])).

fof(f409,plain,
    ( spl4_23
  <=> k1_xboole_0 != k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f455,plain,
    ( spl4_27
  <=> k1_xboole_0 != sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f533,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | sK0 = X2 )
    | ~ spl4_14
    | ~ spl4_23
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f532,f410])).

fof(f410,plain,
    ( k1_xboole_0 != k3_xboole_0(sK1,sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f409])).

fof(f532,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | sK0 = X2 )
    | ~ spl4_14
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f528,f456])).

fof(f456,plain,
    ( k1_xboole_0 != sK0
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f455])).

fof(f528,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | sK0 = X2 )
    | ~ spl4_14 ),
    inference(superposition,[],[f32,f291])).

fof(f526,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f525,f53,f96])).

fof(f96,plain,
    ( spl4_8
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f53,plain,
    ( spl4_2
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f525,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(resolution,[],[f54,f30])).

fof(f54,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f524,plain,
    ( spl4_23
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl4_23
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f516,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f38,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t138_zfmisc_1.p',t2_boole)).

fof(f516,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK3)
    | ~ spl4_23
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f504,f410])).

fof(f504,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl4_30
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f521,plain,
    ( spl4_5
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f513,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f31,f29])).

fof(f513,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_5
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f504,f61])).

fof(f518,plain,
    ( spl4_1
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f511,f40])).

fof(f40,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t138_zfmisc_1.p',t113_zfmisc_1)).

fof(f511,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) != k1_xboole_0
    | ~ spl4_1
    | ~ spl4_30 ),
    inference(backward_demodulation,[],[f504,f47])).

fof(f47,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl4_1
  <=> k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f508,plain,
    ( spl4_30
    | spl4_32
    | spl4_17
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f498,f394,f305,f506,f503])).

fof(f498,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = sK1
        | k3_xboole_0(sK0,sK2) = X2 )
    | ~ spl4_17
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f494,f306])).

fof(f494,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = k3_xboole_0(sK0,sK2)
        | k1_xboole_0 = sK1
        | k3_xboole_0(sK0,sK2) = X2 )
    | ~ spl4_20 ),
    inference(superposition,[],[f32,f395])).

fof(f490,plain,
    ( spl4_28
    | ~ spl4_14
    | spl4_23
    | spl4_27 ),
    inference(avatar_split_clause,[],[f489,f455,f409,f290,f461])).

fof(f489,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | sK0 = X2 )
    | ~ spl4_14
    | ~ spl4_23
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f488,f410])).

fof(f488,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | sK0 = X2 )
    | ~ spl4_14
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f484,f456])).

fof(f484,plain,
    ( ! [X2,X3] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X2,X3)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | sK0 = X2 )
    | ~ spl4_14 ),
    inference(superposition,[],[f32,f291])).

fof(f482,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f481,f53,f96])).

fof(f481,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(resolution,[],[f54,f30])).

fof(f480,plain,
    ( spl4_17
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f470,f71])).

fof(f470,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK2)
    | ~ spl4_17
    | ~ spl4_26 ),
    inference(backward_demodulation,[],[f459,f306])).

fof(f459,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl4_26
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f475,plain,
    ( spl4_7
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f474])).

fof(f474,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f466,f69])).

fof(f466,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl4_7
    | ~ spl4_26 ),
    inference(backward_demodulation,[],[f459,f67])).

fof(f472,plain,
    ( spl4_1
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f464,f41])).

fof(f41,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f464,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) != k1_xboole_0
    | ~ spl4_1
    | ~ spl4_26 ),
    inference(backward_demodulation,[],[f459,f47])).

fof(f463,plain,
    ( spl4_26
    | spl4_28
    | ~ spl4_14
    | spl4_23 ),
    inference(avatar_split_clause,[],[f453,f409,f290,f461,f458])).

fof(f453,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X6,X7)
        | k1_xboole_0 = sK0
        | sK0 = X6 )
    | ~ spl4_14
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f446,f410])).

fof(f446,plain,
    ( ! [X6,X7] :
        ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X6,X7)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | sK0 = X6 )
    | ~ spl4_14 ),
    inference(superposition,[],[f32,f291])).

fof(f438,plain,
    ( spl4_1
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f436,f47])).

fof(f436,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f423,f40])).

fof(f423,plain,
    ( k2_zfmisc_1(sK0,k1_xboole_0) = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_14
    | ~ spl4_22 ),
    inference(backward_demodulation,[],[f413,f291])).

fof(f413,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl4_22
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f435,plain,
    ( spl4_1
    | ~ spl4_12
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f433,f47])).

fof(f433,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl4_12
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f422,f40])).

fof(f422,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl4_12
    | ~ spl4_22 ),
    inference(backward_demodulation,[],[f413,f217])).

fof(f217,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl4_12
  <=> k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f417,plain,
    ( spl4_22
    | spl4_24
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f386,f216,f415,f412])).

fof(f415,plain,
    ( spl4_24
  <=> ! [X6] :
        ( k2_zfmisc_1(k3_xboole_0(X6,sK0),sK1) != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f386,plain,
    ( ! [X6] :
        ( k2_zfmisc_1(k3_xboole_0(X6,sK0),sK1) != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(sK1,sK3)
        | k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(sK0,sK2)) )
    | ~ spl4_12 ),
    inference(superposition,[],[f35,f261])).

fof(f261,plain,
    ( ! [X0] : k2_zfmisc_1(k3_xboole_0(X0,sK0),sK1) = k2_zfmisc_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f241,f39])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t138_zfmisc_1.p',idempotence_k3_xboole_0)).

fof(f241,plain,
    ( ! [X0] : k2_zfmisc_1(k3_xboole_0(X0,sK0),k3_xboole_0(sK1,sK1)) = k2_zfmisc_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK2)),k3_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(superposition,[],[f231,f109])).

fof(f109,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f90,f38])).

fof(f231,plain,
    ( ! [X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,sK0),k3_xboole_0(X1,sK1)) = k2_zfmisc_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK2)),k3_xboole_0(X1,k3_xboole_0(sK1,sK3)))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f228,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t138_zfmisc_1.p',t123_zfmisc_1)).

fof(f228,plain,
    ( ! [X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,k3_xboole_0(sK0,sK2)),k3_xboole_0(X1,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_12 ),
    inference(superposition,[],[f34,f217])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f400,plain,
    ( spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f399,f216,f394])).

fof(f399,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f398,f109])).

fof(f398,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f397,f38])).

fof(f397,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),sK0),sK1)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f378,f217])).

fof(f378,plain,
    ( k2_zfmisc_1(k3_xboole_0(k3_xboole_0(sK0,sK2),sK0),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(superposition,[],[f261,f39])).

fof(f396,plain,
    ( spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f389,f216,f394])).

fof(f389,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f388,f38])).

fof(f388,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f377,f217])).

fof(f377,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(superposition,[],[f261,f125])).

fof(f328,plain,
    ( spl4_1
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f326,f47])).

fof(f326,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(forward_demodulation,[],[f316,f41])).

fof(f316,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(sK1,sK3))
    | ~ spl4_12
    | ~ spl4_16 ),
    inference(backward_demodulation,[],[f309,f217])).

fof(f309,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl4_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f313,plain,
    ( spl4_16
    | spl4_18
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f282,f216,f311,f308])).

fof(f311,plain,
    ( spl4_18
  <=> ! [X6] :
        ( k2_zfmisc_1(sK0,k3_xboole_0(X6,sK1)) != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(sK1,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f282,plain,
    ( ! [X6] :
        ( k2_zfmisc_1(sK0,k3_xboole_0(X6,sK1)) != k1_xboole_0
        | k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(sK1,sK3))
        | k1_xboole_0 = k3_xboole_0(sK0,sK2) )
    | ~ spl4_12 ),
    inference(superposition,[],[f35,f252])).

fof(f252,plain,
    ( ! [X0] : k2_zfmisc_1(sK0,k3_xboole_0(X0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,k3_xboole_0(sK1,sK3)))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f233,f39])).

fof(f233,plain,
    ( ! [X0] : k2_zfmisc_1(k3_xboole_0(sK0,sK0),k3_xboole_0(X0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X0,k3_xboole_0(sK1,sK3)))
    | ~ spl4_12 ),
    inference(superposition,[],[f231,f109])).

fof(f296,plain,
    ( spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f295,f216,f290])).

fof(f295,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f294,f217])).

fof(f294,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f293,f109])).

fof(f293,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK3)))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f274,f38])).

fof(f274,plain,
    ( k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(k3_xboole_0(sK1,sK3),sK1))
    | ~ spl4_12 ),
    inference(superposition,[],[f252,f39])).

fof(f292,plain,
    ( spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f285,f216,f290])).

fof(f285,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f284,f38])).

fof(f284,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK1))
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f273,f217])).

fof(f273,plain,
    ( k2_zfmisc_1(sK0,k3_xboole_0(sK3,sK1)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_12 ),
    inference(superposition,[],[f252,f125])).

fof(f226,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f225,f169,f216])).

fof(f169,plain,
    ( spl4_10
  <=> k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f225,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f224,f38])).

fof(f224,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),k3_xboole_0(sK1,sK3))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f194,f38])).

fof(f194,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),k3_xboole_0(sK3,sK1))
    | ~ spl4_10 ),
    inference(superposition,[],[f170,f34])).

fof(f170,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f169])).

fof(f223,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f193,f96,f216])).

fof(f193,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_8 ),
    inference(superposition,[],[f97,f34])).

fof(f97,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f221,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f220,f169,f216])).

fof(f220,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f219,f38])).

fof(f219,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),k3_xboole_0(sK1,sK3))
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f189,f38])).

fof(f189,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),k3_xboole_0(sK3,sK1))
    | ~ spl4_10 ),
    inference(superposition,[],[f34,f170])).

fof(f218,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f188,f96,f216])).

fof(f188,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3))
    | ~ spl4_8 ),
    inference(superposition,[],[f34,f97])).

fof(f171,plain,
    ( spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f154,f96,f169])).

fof(f154,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_8 ),
    inference(superposition,[],[f125,f97])).

fof(f98,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f88,f53,f96])).

fof(f88,plain,
    ( k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(resolution,[],[f30,f54])).

fof(f68,plain,
    ( ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f26,f66,f60])).

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k2_zfmisc_1(X0,X1) != k1_xboole_0
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t138_zfmisc_1.p',t138_zfmisc_1)).

fof(f55,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f28,f46])).

fof(f28,plain,(
    k2_zfmisc_1(sK0,sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
