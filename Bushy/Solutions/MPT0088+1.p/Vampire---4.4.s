%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t81_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:33 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 117 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 234 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f56,f63,f73,f82,f92,f99,f124,f146,f177,f184])).

fof(f184,plain,
    ( ~ spl3_14
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f182,f163])).

fof(f163,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) = k1_xboole_0
    | ~ spl3_14 ),
    inference(superposition,[],[f42,f123])).

fof(f123,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_14
  <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t81_xboole_1.p',t49_xboole_1)).

fof(f182,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k1_xboole_0
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f169,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t81_xboole_1.p',commutativity_k3_xboole_0)).

fof(f169,plain,
    ( k4_xboole_0(k3_xboole_0(sK1,sK0),sK2) != k1_xboole_0
    | ~ spl3_17 ),
    inference(superposition,[],[f145,f42])).

fof(f145,plain,
    ( k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k1_xboole_0
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_17
  <=> k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f177,plain,
    ( ~ spl3_6
    | ~ spl3_14
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f175,f72])).

fof(f72,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f175,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f163,f152])).

fof(f152,plain,
    ( ~ v1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),sK2))
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f151,f37])).

fof(f151,plain,
    ( ~ v1_xboole_0(k4_xboole_0(k3_xboole_0(sK1,sK0),sK2))
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f150,f42])).

fof(f150,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f72,f145,f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/xboole_1__t81_xboole_1.p',t8_boole)).

fof(f146,plain,
    ( ~ spl3_17
    | spl3_5 ),
    inference(avatar_split_clause,[],[f125,f61,f144])).

fof(f61,plain,
    ( spl3_5
  <=> ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f125,plain,
    ( k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k1_xboole_0
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f62,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
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
    file('/export/starexec/sandbox2/benchmark/xboole_1__t81_xboole_1.p',d7_xboole_0)).

fof(f62,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f124,plain,
    ( spl3_14
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f113,f54,f122])).

fof(f54,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f113,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f99,plain,
    ( ~ spl3_13
    | spl3_5 ),
    inference(avatar_split_clause,[],[f84,f61,f97])).

fof(f97,plain,
    ( spl3_13
  <=> ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f84,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f62,f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/xboole_1__t81_xboole_1.p',symmetry_r1_xboole_0)).

fof(f92,plain,
    ( spl3_10
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f83,f54,f90])).

fof(f90,plain,
    ( spl3_10
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f83,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f55,f38])).

fof(f82,plain,
    ( spl3_8
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f64,f47,f80])).

fof(f80,plain,
    ( spl3_8
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f47,plain,
    ( spl3_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f64,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f48,f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/xboole_1__t81_xboole_1.p',t6_boole)).

fof(f48,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f47])).

fof(f73,plain,
    ( spl3_6
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f66,f47,f71])).

fof(f66,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_0 ),
    inference(backward_demodulation,[],[f64,f48])).

fof(f63,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f30,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t81_xboole_1.p',t81_xboole_1)).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f49,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f31,f47])).

fof(f31,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t81_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
