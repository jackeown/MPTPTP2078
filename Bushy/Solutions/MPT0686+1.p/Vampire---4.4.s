%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t141_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:15 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 202 expanded)
%              Number of leaves         :   23 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  272 ( 553 expanded)
%              Number of equality atoms :   32 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f75,f82,f89,f99,f108,f117,f125,f135,f155,f169,f191,f215,f225,f230,f235])).

fof(f235,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_20
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f233,f98])).

fof(f98,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f233,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f232,f134])).

fof(f134,plain,
    ( k10_relat_1(sK0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_16
  <=> k10_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f232,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK0,k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f231,f168])).

fof(f168,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_20
  <=> k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f231,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f218,f207])).

fof(f207,plain,
    ( ! [X0,X1] : k10_relat_1(sK0,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(sK0,X0),k10_relat_1(sK0,X1))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f67,f74,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t141_funct_1.p',t137_funct_1)).

fof(f74,plain,
    ( v1_funct_1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f67,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f218,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)))
    | ~ spl4_8
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f98,f214,f59])).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t141_funct_1.p',t8_boole)).

fof(f214,plain,
    ( k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) != k1_xboole_0
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl4_25
  <=> k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f230,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_20
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f228,f98])).

fof(f228,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f227,f134])).

fof(f227,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK0,k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f226,f168])).

fof(f226,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f219,f207])).

fof(f219,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)))
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f214,f49])).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t141_funct_1.p',t6_boole)).

fof(f225,plain,
    ( ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_20
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f223,f98])).

fof(f223,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f222,f134])).

fof(f222,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK0,k1_xboole_0))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_20
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f221,f168])).

fof(f221,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK0,k3_xboole_0(sK1,sK2)))
    | ~ spl4_0
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f220,f207])).

fof(f220,plain,
    ( ~ v1_xboole_0(k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)))
    | ~ spl4_8
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f98,f214,f59])).

fof(f215,plain,
    ( ~ spl4_25
    | spl4_15 ),
    inference(avatar_split_clause,[],[f170,f123,f213])).

fof(f123,plain,
    ( spl4_15
  <=> ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f170,plain,
    ( k3_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) != k1_xboole_0
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f124,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t141_funct_1.p',d7_xboole_0)).

fof(f124,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f191,plain,
    ( spl4_22
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f159,f115,f189])).

fof(f189,plain,
    ( spl4_22
  <=> k3_xboole_0(sK2,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f115,plain,
    ( spl4_12
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f159,plain,
    ( k3_xboole_0(sK2,sK1) = k1_xboole_0
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f116,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f116,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f169,plain,
    ( spl4_20
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f158,f87,f167])).

fof(f87,plain,
    ( spl4_6
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f158,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f88,f57])).

fof(f88,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f155,plain,
    ( ~ spl4_19
    | spl4_15 ),
    inference(avatar_split_clause,[],[f126,f123,f153])).

fof(f153,plain,
    ( spl4_19
  <=> ~ r1_xboole_0(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f126,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK2),k10_relat_1(sK0,sK1))
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f124,f56])).

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
    file('/export/starexec/sandbox/benchmark/funct_1__t141_funct_1.p',symmetry_r1_xboole_0)).

fof(f135,plain,
    ( spl4_16
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f128,f66,f133])).

fof(f128,plain,
    ( k10_relat_1(sK0,k1_xboole_0) = k1_xboole_0
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f67,f48])).

fof(f48,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t141_funct_1.p',t171_relat_1)).

fof(f125,plain,(
    ~ spl4_15 ),
    inference(avatar_split_clause,[],[f45,f123])).

fof(f45,plain,(
    ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_xboole_0(k10_relat_1(sK0,sK1),k10_relat_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
            & r1_xboole_0(X1,X2) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( ~ r1_xboole_0(k10_relat_1(sK0,X1),k10_relat_1(sK0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
     => ( ~ r1_xboole_0(k10_relat_1(X0,sK1),k10_relat_1(X0,sK2))
        & r1_xboole_0(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          & r1_xboole_0(X1,X2) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_xboole_0(X1,X2)
           => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t141_funct_1.p',t141_funct_1)).

fof(f117,plain,
    ( spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f110,f87,f115])).

fof(f110,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f88,f56])).

fof(f108,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f90,f80,f106])).

fof(f106,plain,
    ( spl4_10
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f80,plain,
    ( spl4_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f90,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f81,f49])).

fof(f81,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f99,plain,
    ( spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f92,f80,f97])).

fof(f92,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f90,f81])).

fof(f89,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f44,f87])).

fof(f44,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t141_funct_1.p',dt_o_0_0_xboole_0)).

fof(f75,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f43,f73])).

fof(f43,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f68,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f42,f66])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
