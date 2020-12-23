%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t77_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:32 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 154 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :    7
%              Number of atoms          :  183 ( 337 expanded)
%              Number of equality atoms :   38 (  70 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f55,f62,f69,f79,f88,f98,f107,f127,f139,f146,f173,f184,f214,f219])).

fof(f219,plain,
    ( spl3_13
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl3_13
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f217,f152])).

fof(f152,plain,
    ( k3_xboole_0(sK1,sK0) != k1_xboole_0
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f97,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/xboole_1__t77_xboole_1.p',d7_xboole_0)).

fof(f97,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_13
  <=> ~ r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f217,plain,
    ( k3_xboole_0(sK1,sK0) = k1_xboole_0
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f216,f126])).

fof(f126,plain,
    ( k3_xboole_0(sK0,sK2) = sK0
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_16
  <=> k3_xboole_0(sK0,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f216,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK0,sK2)) = k1_xboole_0
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f199,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t77_xboole_1.p',commutativity_k3_xboole_0)).

fof(f199,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)) = k1_xboole_0
    | ~ spl3_20 ),
    inference(superposition,[],[f145,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t77_xboole_1.p',t16_xboole_1)).

fof(f145,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) = k1_xboole_0
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_20
  <=> k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f214,plain,
    ( spl3_13
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl3_13
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f212,f152])).

fof(f212,plain,
    ( k3_xboole_0(sK1,sK0) = k1_xboole_0
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f211,f126])).

fof(f211,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK0,sK2)) = k1_xboole_0
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f194,f35])).

fof(f194,plain,
    ( k3_xboole_0(sK1,k3_xboole_0(sK2,sK0)) = k1_xboole_0
    | ~ spl3_20 ),
    inference(superposition,[],[f41,f145])).

fof(f184,plain,
    ( ~ spl3_25
    | ~ spl3_8
    | spl3_23 ),
    inference(avatar_split_clause,[],[f177,f171,f77,f182])).

fof(f182,plain,
    ( spl3_25
  <=> ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f77,plain,
    ( spl3_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f171,plain,
    ( spl3_23
  <=> k3_xboole_0(sK0,sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f177,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(unit_resulting_resolution,[],[f78,f172,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t77_xboole_1.p',t8_boole)).

fof(f172,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f171])).

fof(f78,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f173,plain,
    ( ~ spl3_23
    | spl3_3 ),
    inference(avatar_split_clause,[],[f151,f53,f171])).

fof(f53,plain,
    ( spl3_3
  <=> ~ r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f151,plain,
    ( k3_xboole_0(sK0,sK1) != k1_xboole_0
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f54,f39])).

fof(f54,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f146,plain,
    ( spl3_20
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f129,f105,f144])).

fof(f105,plain,
    ( spl3_14
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f129,plain,
    ( k3_xboole_0(k3_xboole_0(sK1,sK2),sK0) = k1_xboole_0
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f106,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f105])).

fof(f139,plain,
    ( spl3_18
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f128,f67,f137])).

fof(f137,plain,
    ( spl3_18
  <=> k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f67,plain,
    ( spl3_6
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f128,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) = k1_xboole_0
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f68,f38])).

fof(f68,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f127,plain,
    ( spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f119,f60,f125])).

fof(f60,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f119,plain,
    ( k3_xboole_0(sK0,sK2) = sK0
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f61,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t77_xboole_1.p',t28_xboole_1)).

fof(f61,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f107,plain,
    ( spl3_14
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f89,f67,f105])).

fof(f89,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t77_xboole_1.p',symmetry_r1_xboole_0)).

fof(f98,plain,
    ( ~ spl3_13
    | spl3_3 ),
    inference(avatar_split_clause,[],[f90,f53,f96])).

fof(f90,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f54,f37])).

fof(f88,plain,
    ( spl3_10
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f70,f46,f86])).

fof(f86,plain,
    ( spl3_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f46,plain,
    ( spl3_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f70,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t77_xboole_1.p',t6_boole)).

fof(f47,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f46])).

fof(f79,plain,
    ( spl3_8
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f72,f46,f77])).

fof(f72,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_0 ),
    inference(backward_demodulation,[],[f70,f47])).

fof(f69,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t77_xboole_1.p',t77_xboole_1)).

fof(f62,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f28,f53])).

fof(f28,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f31,f46])).

fof(f31,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t77_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
