%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t125_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:14 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 213 expanded)
%              Number of leaves         :   23 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 ( 646 expanded)
%              Number of equality atoms :   32 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f243,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f75,f82,f89,f96,f106,f115,f124,f132,f142,f159,f190,f198,f222,f232,f237,f242])).

fof(f242,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_22
    | spl4_27 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f240,f105])).

fof(f105,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f240,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f239,f141])).

fof(f141,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl4_18
  <=> k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f239,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f238,f189])).

fof(f189,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_22
  <=> k3_xboole_0(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f238,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f225,f199])).

fof(f199,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f67,f74,f81,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t125_funct_1.p',t121_funct_1)).

fof(f81,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f67,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f225,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(unit_resulting_resolution,[],[f105,f221,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t125_funct_1.p',t8_boole)).

fof(f221,plain,
    ( k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k1_xboole_0
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_27
  <=> k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f237,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_22
    | spl4_27 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f235,f105])).

fof(f235,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f234,f141])).

fof(f234,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f233,f189])).

fof(f233,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f226,f199])).

fof(f226,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | ~ spl4_27 ),
    inference(unit_resulting_resolution,[],[f221,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t125_funct_1.p',t6_boole)).

fof(f232,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_22
    | spl4_27 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f230,f105])).

fof(f230,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f229,f141])).

fof(f229,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_22
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f228,f189])).

fof(f228,plain,
    ( ~ v1_xboole_0(k9_relat_1(sK2,k3_xboole_0(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f227,f199])).

fof(f227,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)))
    | ~ spl4_10
    | ~ spl4_27 ),
    inference(unit_resulting_resolution,[],[f105,f221,f59])).

fof(f222,plain,
    ( ~ spl4_27
    | spl4_17 ),
    inference(avatar_split_clause,[],[f170,f130,f220])).

fof(f130,plain,
    ( spl4_17
  <=> ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f170,plain,
    ( k3_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) != k1_xboole_0
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f131,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t125_funct_1.p',d7_xboole_0)).

fof(f131,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f130])).

fof(f198,plain,
    ( spl4_24
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f166,f122,f196])).

fof(f196,plain,
    ( spl4_24
  <=> k3_xboole_0(sK1,sK0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f122,plain,
    ( spl4_14
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f166,plain,
    ( k3_xboole_0(sK1,sK0) = k1_xboole_0
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f123,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f123,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f190,plain,
    ( spl4_22
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f165,f94,f188])).

fof(f94,plain,
    ( spl4_8
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f165,plain,
    ( k3_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f95,f57])).

fof(f95,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f159,plain,
    ( ~ spl4_21
    | spl4_17 ),
    inference(avatar_split_clause,[],[f133,f130,f157])).

fof(f157,plain,
    ( spl4_21
  <=> ~ r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f133,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK1),k9_relat_1(sK2,sK0))
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f131,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t125_funct_1.p',symmetry_r1_xboole_0)).

fof(f142,plain,
    ( spl4_18
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f135,f66,f140])).

fof(f135,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f67,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t125_funct_1.p',t149_relat_1)).

fof(f132,plain,(
    ~ spl4_17 ),
    inference(avatar_split_clause,[],[f45,f130])).

fof(f45,plain,(
    ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v2_funct_1(sK2)
    & r1_xboole_0(sK0,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v2_funct_1(sK2)
      & r1_xboole_0(sK0,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t125_funct_1.p',t125_funct_1)).

fof(f124,plain,
    ( spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f117,f94,f122])).

fof(f117,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f95,f56])).

fof(f115,plain,
    ( spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f97,f87,f113])).

fof(f113,plain,
    ( spl4_12
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f87,plain,
    ( spl4_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f97,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f88,f49])).

fof(f88,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f106,plain,
    ( spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f99,f87,f104])).

fof(f99,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f97,f88])).

fof(f96,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f46,f87])).

fof(f46,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t125_funct_1.p',dt_o_0_0_xboole_0)).

fof(f82,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f44,f80])).

fof(f44,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f42,f73])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f41,f66])).

fof(f41,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
