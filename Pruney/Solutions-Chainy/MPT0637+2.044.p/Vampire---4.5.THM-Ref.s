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
% DateTime   : Thu Dec  3 12:52:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 141 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :    6
%              Number of atoms          :  215 ( 323 expanded)
%              Number of equality atoms :   67 ( 103 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f42,f46,f50,f54,f62,f66,f70,f74,f88,f94,f100,f106,f112,f127,f141,f165,f183])).

fof(f183,plain,
    ( spl2_15
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl2_15
    | ~ spl2_23 ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_15
    | ~ spl2_23 ),
    inference(superposition,[],[f99,f159])).

fof(f159,plain,
    ( ! [X2,X3] : k6_relat_1(k3_xboole_0(X2,X3)) = k8_relat_1(X2,k6_relat_1(X3))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl2_23
  <=> ! [X3,X2] : k6_relat_1(k3_xboole_0(X2,X3)) = k8_relat_1(X2,k6_relat_1(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f99,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_15
  <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k8_relat_1(sK0,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f165,plain,
    ( spl2_23
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f155,f138,f110,f158])).

fof(f110,plain,
    ( spl2_17
  <=> ! [X1,X0] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f138,plain,
    ( spl2_21
  <=> ! [X3,X2] : k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3))) = k8_relat_1(X2,k6_relat_1(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f155,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_17
    | ~ spl2_21 ),
    inference(superposition,[],[f111,f139])).

fof(f139,plain,
    ( ! [X2,X3] : k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3))) = k8_relat_1(X2,k6_relat_1(X3))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f138])).

fof(f111,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f110])).

fof(f141,plain,
    ( spl2_21
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f131,f125,f92,f138])).

fof(f92,plain,
    ( spl2_14
  <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f125,plain,
    ( spl2_19
  <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f131,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1)))
    | ~ spl2_14
    | ~ spl2_19 ),
    inference(superposition,[],[f93,f126])).

fof(f126,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f93,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f127,plain,
    ( spl2_19
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f123,f92,f68,f48,f40,f125])).

fof(f40,plain,
    ( spl2_3
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f48,plain,
    ( spl2_5
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f68,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f123,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f122,f93])).

fof(f122,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f121,f49])).

fof(f49,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f121,plain,
    ( ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f69,f41])).

fof(f41,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f112,plain,
    ( spl2_17
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f107,f104,f52,f110])).

fof(f52,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f104,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f107,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1)))
    | ~ spl2_6
    | ~ spl2_16 ),
    inference(resolution,[],[f105,f53])).

fof(f53,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f102,f72,f44,f40,f104])).

fof(f44,plain,
    ( spl2_4
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f72,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f101,f45])).

fof(f45,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
        | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_3
    | ~ spl2_11 ),
    inference(resolution,[],[f73,f41])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k8_relat_1(X0,X1) = X1 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f100,plain,
    ( ~ spl2_15
    | spl2_1
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f95,f86,f31,f97])).

fof(f31,plain,
    ( spl2_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f86,plain,
    ( spl2_13
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f95,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_1
    | ~ spl2_13 ),
    inference(superposition,[],[f33,f87])).

fof(f87,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f33,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f94,plain,
    ( spl2_14
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f90,f86,f64,f40,f92])).

fof(f64,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f90,plain,
    ( ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f89,f87])).

fof(f89,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(resolution,[],[f65,f41])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f88,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f84,f60,f40,f86])).

fof(f60,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f84,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))
    | ~ spl2_3
    | ~ spl2_8 ),
    inference(resolution,[],[f61,f41])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f74,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f70,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

fof(f66,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f62,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f54,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f50,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f46,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f34,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f31])).

fof(f19,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:55:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.44  % (18641)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.23/0.44  % (18640)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.23/0.45  % (18639)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.23/0.45  % (18642)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.23/0.45  % (18640)Refutation found. Thanks to Tanya!
% 0.23/0.45  % SZS status Theorem for theBenchmark
% 0.23/0.45  % SZS output start Proof for theBenchmark
% 0.23/0.45  fof(f184,plain,(
% 0.23/0.45    $false),
% 0.23/0.45    inference(avatar_sat_refutation,[],[f34,f42,f46,f50,f54,f62,f66,f70,f74,f88,f94,f100,f106,f112,f127,f141,f165,f183])).
% 0.23/0.45  fof(f183,plain,(
% 0.23/0.45    spl2_15 | ~spl2_23),
% 0.23/0.45    inference(avatar_contradiction_clause,[],[f182])).
% 0.23/0.45  fof(f182,plain,(
% 0.23/0.45    $false | (spl2_15 | ~spl2_23)),
% 0.23/0.45    inference(trivial_inequality_removal,[],[f169])).
% 0.23/0.45  fof(f169,plain,(
% 0.23/0.45    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) | (spl2_15 | ~spl2_23)),
% 0.23/0.45    inference(superposition,[],[f99,f159])).
% 0.23/0.45  fof(f159,plain,(
% 0.23/0.45    ( ! [X2,X3] : (k6_relat_1(k3_xboole_0(X2,X3)) = k8_relat_1(X2,k6_relat_1(X3))) ) | ~spl2_23),
% 0.23/0.45    inference(avatar_component_clause,[],[f158])).
% 0.23/0.45  fof(f158,plain,(
% 0.23/0.45    spl2_23 <=> ! [X3,X2] : k6_relat_1(k3_xboole_0(X2,X3)) = k8_relat_1(X2,k6_relat_1(X3))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.23/0.45  fof(f99,plain,(
% 0.23/0.45    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) | spl2_15),
% 0.23/0.45    inference(avatar_component_clause,[],[f97])).
% 0.23/0.45  fof(f97,plain,(
% 0.23/0.45    spl2_15 <=> k6_relat_1(k3_xboole_0(sK0,sK1)) = k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.23/0.45  fof(f165,plain,(
% 0.23/0.45    spl2_23 | ~spl2_17 | ~spl2_21),
% 0.23/0.45    inference(avatar_split_clause,[],[f155,f138,f110,f158])).
% 0.23/0.45  fof(f110,plain,(
% 0.23/0.45    spl2_17 <=> ! [X1,X0] : k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1)))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.23/0.45  fof(f138,plain,(
% 0.23/0.45    spl2_21 <=> ! [X3,X2] : k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3))) = k8_relat_1(X2,k6_relat_1(X3))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.23/0.45  fof(f155,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl2_17 | ~spl2_21)),
% 0.23/0.45    inference(superposition,[],[f111,f139])).
% 0.23/0.45  fof(f139,plain,(
% 0.23/0.45    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3))) = k8_relat_1(X2,k6_relat_1(X3))) ) | ~spl2_21),
% 0.23/0.45    inference(avatar_component_clause,[],[f138])).
% 0.23/0.45  fof(f111,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1)))) ) | ~spl2_17),
% 0.23/0.45    inference(avatar_component_clause,[],[f110])).
% 0.23/0.45  fof(f141,plain,(
% 0.23/0.45    spl2_21 | ~spl2_14 | ~spl2_19),
% 0.23/0.45    inference(avatar_split_clause,[],[f131,f125,f92,f138])).
% 0.23/0.45  fof(f92,plain,(
% 0.23/0.45    spl2_14 <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.23/0.45  fof(f125,plain,(
% 0.23/0.45    spl2_19 <=> ! [X1,X0] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.23/0.45  fof(f131,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1)))) ) | (~spl2_14 | ~spl2_19)),
% 0.23/0.45    inference(superposition,[],[f93,f126])).
% 0.23/0.45  fof(f126,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | ~spl2_19),
% 0.23/0.45    inference(avatar_component_clause,[],[f125])).
% 0.23/0.45  fof(f93,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_14),
% 0.23/0.45    inference(avatar_component_clause,[],[f92])).
% 0.23/0.45  fof(f127,plain,(
% 0.23/0.45    spl2_19 | ~spl2_3 | ~spl2_5 | ~spl2_10 | ~spl2_14),
% 0.23/0.45    inference(avatar_split_clause,[],[f123,f92,f68,f48,f40,f125])).
% 0.23/0.45  fof(f40,plain,(
% 0.23/0.45    spl2_3 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.45  fof(f48,plain,(
% 0.23/0.45    spl2_5 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.23/0.45  fof(f68,plain,(
% 0.23/0.45    spl2_10 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.23/0.45  fof(f123,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_5 | ~spl2_10 | ~spl2_14)),
% 0.23/0.45    inference(forward_demodulation,[],[f122,f93])).
% 0.23/0.45  fof(f122,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_5 | ~spl2_10)),
% 0.23/0.45    inference(forward_demodulation,[],[f121,f49])).
% 0.23/0.45  fof(f49,plain,(
% 0.23/0.45    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.23/0.45    inference(avatar_component_clause,[],[f48])).
% 0.23/0.45  fof(f121,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) ) | (~spl2_3 | ~spl2_10)),
% 0.23/0.45    inference(resolution,[],[f69,f41])).
% 0.23/0.45  fof(f41,plain,(
% 0.23/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_3),
% 0.23/0.45    inference(avatar_component_clause,[],[f40])).
% 0.23/0.45  fof(f69,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))) ) | ~spl2_10),
% 0.23/0.45    inference(avatar_component_clause,[],[f68])).
% 0.23/0.45  fof(f112,plain,(
% 0.23/0.45    spl2_17 | ~spl2_6 | ~spl2_16),
% 0.23/0.45    inference(avatar_split_clause,[],[f107,f104,f52,f110])).
% 0.23/0.45  fof(f52,plain,(
% 0.23/0.45    spl2_6 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.23/0.45  fof(f104,plain,(
% 0.23/0.45    spl2_16 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.23/0.45  fof(f107,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1)))) ) | (~spl2_6 | ~spl2_16)),
% 0.23/0.45    inference(resolution,[],[f105,f53])).
% 0.23/0.45  fof(f53,plain,(
% 0.23/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_6),
% 0.23/0.45    inference(avatar_component_clause,[],[f52])).
% 0.23/0.45  fof(f105,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_16),
% 0.23/0.45    inference(avatar_component_clause,[],[f104])).
% 0.23/0.45  fof(f106,plain,(
% 0.23/0.45    spl2_16 | ~spl2_3 | ~spl2_4 | ~spl2_11),
% 0.23/0.45    inference(avatar_split_clause,[],[f102,f72,f44,f40,f104])).
% 0.23/0.45  fof(f44,plain,(
% 0.23/0.45    spl2_4 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.23/0.45  fof(f72,plain,(
% 0.23/0.45    spl2_11 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.23/0.45  fof(f102,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_4 | ~spl2_11)),
% 0.23/0.45    inference(forward_demodulation,[],[f101,f45])).
% 0.23/0.45  fof(f45,plain,(
% 0.23/0.45    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_4),
% 0.23/0.45    inference(avatar_component_clause,[],[f44])).
% 0.23/0.45  fof(f101,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) ) | (~spl2_3 | ~spl2_11)),
% 0.23/0.45    inference(resolution,[],[f73,f41])).
% 0.23/0.45  fof(f73,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) ) | ~spl2_11),
% 0.23/0.45    inference(avatar_component_clause,[],[f72])).
% 0.23/0.45  fof(f100,plain,(
% 0.23/0.45    ~spl2_15 | spl2_1 | ~spl2_13),
% 0.23/0.45    inference(avatar_split_clause,[],[f95,f86,f31,f97])).
% 0.23/0.45  fof(f31,plain,(
% 0.23/0.45    spl2_1 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.45  fof(f86,plain,(
% 0.23/0.45    spl2_13 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.23/0.45  fof(f95,plain,(
% 0.23/0.45    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) | (spl2_1 | ~spl2_13)),
% 0.23/0.45    inference(superposition,[],[f33,f87])).
% 0.23/0.45  fof(f87,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) ) | ~spl2_13),
% 0.23/0.45    inference(avatar_component_clause,[],[f86])).
% 0.23/0.45  fof(f33,plain,(
% 0.23/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.23/0.45    inference(avatar_component_clause,[],[f31])).
% 0.23/0.45  fof(f94,plain,(
% 0.23/0.45    spl2_14 | ~spl2_3 | ~spl2_9 | ~spl2_13),
% 0.23/0.45    inference(avatar_split_clause,[],[f90,f86,f64,f40,f92])).
% 0.23/0.45  fof(f64,plain,(
% 0.23/0.45    spl2_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.23/0.45  fof(f90,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_9 | ~spl2_13)),
% 0.23/0.45    inference(forward_demodulation,[],[f89,f87])).
% 0.23/0.45  fof(f89,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_3 | ~spl2_9)),
% 0.23/0.45    inference(resolution,[],[f65,f41])).
% 0.23/0.45  fof(f65,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_9),
% 0.23/0.45    inference(avatar_component_clause,[],[f64])).
% 0.23/0.45  fof(f88,plain,(
% 0.23/0.45    spl2_13 | ~spl2_3 | ~spl2_8),
% 0.23/0.45    inference(avatar_split_clause,[],[f84,f60,f40,f86])).
% 0.23/0.45  fof(f60,plain,(
% 0.23/0.45    spl2_8 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.23/0.45  fof(f84,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) ) | (~spl2_3 | ~spl2_8)),
% 0.23/0.45    inference(resolution,[],[f61,f41])).
% 0.23/0.45  fof(f61,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) ) | ~spl2_8),
% 0.23/0.45    inference(avatar_component_clause,[],[f60])).
% 0.23/0.45  fof(f74,plain,(
% 0.23/0.45    spl2_11),
% 0.23/0.45    inference(avatar_split_clause,[],[f29,f72])).
% 0.23/0.45  fof(f29,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f16])).
% 0.23/0.45  fof(f16,plain,(
% 0.23/0.45    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.23/0.45    inference(flattening,[],[f15])).
% 0.23/0.45  fof(f15,plain,(
% 0.23/0.45    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.45    inference(ennf_transformation,[],[f4])).
% 0.23/0.45  fof(f4,axiom,(
% 0.23/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.23/0.45  fof(f70,plain,(
% 0.23/0.45    spl2_10),
% 0.23/0.45    inference(avatar_split_clause,[],[f28,f68])).
% 0.23/0.45  fof(f28,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f14])).
% 0.23/0.45  fof(f14,plain,(
% 0.23/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.23/0.45    inference(ennf_transformation,[],[f5])).
% 0.23/0.45  fof(f5,axiom,(
% 0.23/0.45    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).
% 0.23/0.45  fof(f66,plain,(
% 0.23/0.45    spl2_9),
% 0.23/0.45    inference(avatar_split_clause,[],[f27,f64])).
% 0.23/0.45  fof(f27,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f13])).
% 0.23/0.45  fof(f13,plain,(
% 0.23/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.23/0.45    inference(ennf_transformation,[],[f7])).
% 0.23/0.45  fof(f7,axiom,(
% 0.23/0.45    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.23/0.45  fof(f62,plain,(
% 0.23/0.45    spl2_8),
% 0.23/0.45    inference(avatar_split_clause,[],[f26,f60])).
% 0.23/0.45  fof(f26,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f12])).
% 0.23/0.45  fof(f12,plain,(
% 0.23/0.45    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.23/0.45    inference(ennf_transformation,[],[f3])).
% 0.23/0.45  fof(f3,axiom,(
% 0.23/0.45    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.23/0.45  fof(f54,plain,(
% 0.23/0.45    spl2_6),
% 0.23/0.45    inference(avatar_split_clause,[],[f24,f52])).
% 0.23/0.45  fof(f24,plain,(
% 0.23/0.45    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f2])).
% 0.23/0.45  fof(f2,axiom,(
% 0.23/0.45    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.23/0.45  fof(f50,plain,(
% 0.23/0.45    spl2_5),
% 0.23/0.45    inference(avatar_split_clause,[],[f22,f48])).
% 0.23/0.45  fof(f22,plain,(
% 0.23/0.45    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.45    inference(cnf_transformation,[],[f6])).
% 0.23/0.45  fof(f6,axiom,(
% 0.23/0.45    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.23/0.45  fof(f46,plain,(
% 0.23/0.45    spl2_4),
% 0.23/0.45    inference(avatar_split_clause,[],[f23,f44])).
% 0.23/0.45  fof(f23,plain,(
% 0.23/0.45    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.23/0.45    inference(cnf_transformation,[],[f6])).
% 0.23/0.45  fof(f42,plain,(
% 0.23/0.45    spl2_3),
% 0.23/0.45    inference(avatar_split_clause,[],[f20,f40])).
% 0.23/0.45  fof(f20,plain,(
% 0.23/0.45    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f8])).
% 0.23/0.45  fof(f8,axiom,(
% 0.23/0.45    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.23/0.45  fof(f34,plain,(
% 0.23/0.45    ~spl2_1),
% 0.23/0.45    inference(avatar_split_clause,[],[f19,f31])).
% 0.23/0.45  fof(f19,plain,(
% 0.23/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.23/0.45    inference(cnf_transformation,[],[f18])).
% 0.23/0.45  fof(f18,plain,(
% 0.23/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.23/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 0.23/0.45  fof(f17,plain,(
% 0.23/0.45    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.23/0.45    introduced(choice_axiom,[])).
% 0.23/0.45  fof(f11,plain,(
% 0.23/0.45    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.23/0.45    inference(ennf_transformation,[],[f10])).
% 0.23/0.45  fof(f10,negated_conjecture,(
% 0.23/0.45    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.23/0.45    inference(negated_conjecture,[],[f9])).
% 0.23/0.45  fof(f9,conjecture,(
% 0.23/0.45    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.23/0.45  % SZS output end Proof for theBenchmark
% 0.23/0.45  % (18640)------------------------------
% 0.23/0.45  % (18640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.45  % (18640)Termination reason: Refutation
% 0.23/0.45  
% 0.23/0.45  % (18640)Memory used [KB]: 10618
% 0.23/0.45  % (18640)Time elapsed: 0.008 s
% 0.23/0.45  % (18640)------------------------------
% 0.23/0.45  % (18640)------------------------------
% 0.23/0.45  % (18634)Success in time 0.08 s
%------------------------------------------------------------------------------
