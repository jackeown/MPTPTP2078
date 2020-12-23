%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 261 expanded)
%              Number of leaves         :   27 ( 108 expanded)
%              Depth                    :   10
%              Number of atoms          :  398 ( 820 expanded)
%              Number of equality atoms :   61 ( 118 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f84,f91,f98,f105,f113,f117,f122,f139,f155,f160,f170,f188,f193,f211,f213,f235,f236,f237])).

fof(f237,plain,
    ( k1_funct_1(sK3,sK4) != sK7(sK3,sK2,sK4)
    | r2_hidden(k4_tarski(sK4,k1_funct_1(sK3,sK4)),sK3)
    | ~ r2_hidden(k4_tarski(sK4,sK7(sK3,sK2,sK4)),sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f236,plain,
    ( k1_funct_1(sK3,sK4) != sK7(sK3,sK2,sK4)
    | r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f235,plain,
    ( spl8_17
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f226,f209,f82,f58,f233])).

fof(f233,plain,
    ( spl8_17
  <=> k1_funct_1(sK3,sK4) = sK7(sK3,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f58,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f82,plain,
    ( spl8_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f209,plain,
    ( spl8_16
  <=> r2_hidden(k4_tarski(sK4,sK7(sK3,sK2,sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f226,plain,
    ( k1_funct_1(sK3,sK4) = sK7(sK3,sK2,sK4)
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f225,f83])).

fof(f83,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f225,plain,
    ( k1_funct_1(sK3,sK4) = sK7(sK3,sK2,sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f221,f59])).

fof(f59,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f221,plain,
    ( ~ v1_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = sK7(sK3,sK2,sK4)
    | ~ v1_relat_1(sK3)
    | ~ spl8_16 ),
    inference(resolution,[],[f210,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f210,plain,
    ( r2_hidden(k4_tarski(sK4,sK7(sK3,sK2,sK4)),sK3)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f209])).

fof(f213,plain,
    ( spl8_14
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f212,f103,f82,f153])).

fof(f153,plain,
    ( spl8_14
  <=> sP6(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f103,plain,
    ( spl8_10
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f212,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_5
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f189,f83])).

fof(f189,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_10 ),
    inference(resolution,[],[f108,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | sP6(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f108,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f211,plain,
    ( spl8_16
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f172,f153,f209])).

fof(f172,plain,
    ( r2_hidden(k4_tarski(sK4,sK7(sK3,sK2,sK4)),sK3)
    | ~ spl8_14 ),
    inference(resolution,[],[f154,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(k4_tarski(X3,sK7(X0,X1,X3)),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f193,plain,
    ( spl8_15
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f173,f153,f191])).

fof(f191,plain,
    ( spl8_15
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f173,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl8_14 ),
    inference(resolution,[],[f154,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f188,plain,
    ( spl8_10
    | ~ spl8_5
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f175,f153,f82,f103])).

fof(f175,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_5
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f174,f83])).

fof(f174,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_14 ),
    inference(resolution,[],[f154,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f170,plain,
    ( spl8_7
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f162,f137,f119,f82,f58,f89])).

fof(f89,plain,
    ( spl8_7
  <=> r2_hidden(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f119,plain,
    ( spl8_12
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f137,plain,
    ( spl8_13
  <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK3,sK4)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f162,plain,
    ( r2_hidden(sK4,sK0)
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f161,f120])).

fof(f120,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f161,plain,
    ( r2_hidden(sK4,k1_relat_1(sK3))
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f143,f83])).

fof(f143,plain,
    ( r2_hidden(sK4,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f141,f59])).

fof(f141,plain,
    ( ~ v1_funct_1(sK3)
    | r2_hidden(sK4,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl8_13 ),
    inference(resolution,[],[f138,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f138,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK3,sK4)),sK3)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f160,plain,
    ( ~ spl8_4
    | ~ spl8_6
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_6
    | spl8_10 ),
    inference(subsumption_resolution,[],[f158,f104])).

fof(f104,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f158,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f87,f76])).

fof(f76,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl8_4 ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f87,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_6
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f155,plain,
    ( spl8_14
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f146,f137,f100,f153])).

fof(f100,plain,
    ( spl8_9
  <=> r2_hidden(k1_funct_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f146,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(resolution,[],[f140,f112])).

fof(f112,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4),X0)
        | sP6(sK4,X0,sK3) )
    | ~ spl8_13 ),
    inference(resolution,[],[f138,f32])).

fof(f32,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f139,plain,
    ( spl8_13
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f126,f119,f89,f82,f58,f137])).

fof(f126,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK3,sK4)),sK3)
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_12 ),
    inference(resolution,[],[f125,f90])).

fof(f90,plain,
    ( r2_hidden(sK4,sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) )
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f124,f83])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK3)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) )
    | ~ spl8_1
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f123,f59])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) )
    | ~ spl8_12 ),
    inference(superposition,[],[f49,f120])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f122,plain,
    ( spl8_12
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f121,f115,f96,f119])).

fof(f96,plain,
    ( spl8_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f115,plain,
    ( spl8_11
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f121,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_8
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f116,f97])).

fof(f97,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f116,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f117,plain,
    ( spl8_11
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f73,f70,f115])).

fof(f73,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f71,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f113,plain,
    ( spl8_9
    | ~ spl8_4
    | spl8_10 ),
    inference(avatar_split_clause,[],[f111,f103,f70,f100])).

fof(f111,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f110,f104])).

fof(f110,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f24,f76])).

fof(f24,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
                & r2_hidden(X4,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
          <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_2)).

fof(f105,plain,
    ( ~ spl8_9
    | ~ spl8_10
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f93,f89,f70,f103,f100])).

fof(f93,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f92,f76])).

fof(f92,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f22,f90])).

fof(f22,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f98,plain,
    ( spl8_8
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f79,f70,f66,f62,f96])).

fof(f62,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f66,plain,
    ( spl8_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f79,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f78,f67])).

fof(f67,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f78,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f75,f63])).

fof(f63,plain,
    ( k1_xboole_0 != sK1
    | spl8_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_4 ),
    inference(resolution,[],[f71,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f91,plain,
    ( spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f23,f89,f86])).

fof(f23,plain,
    ( r2_hidden(sK4,sK0)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,
    ( spl8_5
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f80,f70,f82])).

fof(f80,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f77,f47])).

fof(f47,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f77,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(resolution,[],[f71,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f72,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f27,f70])).

fof(f27,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:39:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.44  % (31734)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.45  % (31734)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f238,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f84,f91,f98,f105,f113,f117,f122,f139,f155,f160,f170,f188,f193,f211,f213,f235,f236,f237])).
% 0.20/0.45  fof(f237,plain,(
% 0.20/0.45    k1_funct_1(sK3,sK4) != sK7(sK3,sK2,sK4) | r2_hidden(k4_tarski(sK4,k1_funct_1(sK3,sK4)),sK3) | ~r2_hidden(k4_tarski(sK4,sK7(sK3,sK2,sK4)),sK3)),
% 0.20/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.45  fof(f236,plain,(
% 0.20/0.45    k1_funct_1(sK3,sK4) != sK7(sK3,sK2,sK4) | r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 0.20/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.45  fof(f235,plain,(
% 0.20/0.45    spl8_17 | ~spl8_1 | ~spl8_5 | ~spl8_16),
% 0.20/0.45    inference(avatar_split_clause,[],[f226,f209,f82,f58,f233])).
% 0.20/0.45  fof(f233,plain,(
% 0.20/0.45    spl8_17 <=> k1_funct_1(sK3,sK4) = sK7(sK3,sK2,sK4)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    spl8_1 <=> v1_funct_1(sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    spl8_5 <=> v1_relat_1(sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.45  fof(f209,plain,(
% 0.20/0.45    spl8_16 <=> r2_hidden(k4_tarski(sK4,sK7(sK3,sK2,sK4)),sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.20/0.45  fof(f226,plain,(
% 0.20/0.45    k1_funct_1(sK3,sK4) = sK7(sK3,sK2,sK4) | (~spl8_1 | ~spl8_5 | ~spl8_16)),
% 0.20/0.45    inference(subsumption_resolution,[],[f225,f83])).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    v1_relat_1(sK3) | ~spl8_5),
% 0.20/0.45    inference(avatar_component_clause,[],[f82])).
% 0.20/0.45  fof(f225,plain,(
% 0.20/0.45    k1_funct_1(sK3,sK4) = sK7(sK3,sK2,sK4) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_16)),
% 0.20/0.45    inference(subsumption_resolution,[],[f221,f59])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    v1_funct_1(sK3) | ~spl8_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f58])).
% 0.20/0.45  fof(f221,plain,(
% 0.20/0.45    ~v1_funct_1(sK3) | k1_funct_1(sK3,sK4) = sK7(sK3,sK2,sK4) | ~v1_relat_1(sK3) | ~spl8_16),
% 0.20/0.45    inference(resolution,[],[f210,f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.45    inference(flattening,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.45  fof(f210,plain,(
% 0.20/0.45    r2_hidden(k4_tarski(sK4,sK7(sK3,sK2,sK4)),sK3) | ~spl8_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f209])).
% 0.20/0.45  fof(f213,plain,(
% 0.20/0.45    spl8_14 | ~spl8_5 | ~spl8_10),
% 0.20/0.45    inference(avatar_split_clause,[],[f212,f103,f82,f153])).
% 0.20/0.45  fof(f153,plain,(
% 0.20/0.45    spl8_14 <=> sP6(sK4,sK2,sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.45  fof(f103,plain,(
% 0.20/0.45    spl8_10 <=> r2_hidden(sK4,k10_relat_1(sK3,sK2))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.45  fof(f212,plain,(
% 0.20/0.45    sP6(sK4,sK2,sK3) | (~spl8_5 | ~spl8_10)),
% 0.20/0.45    inference(subsumption_resolution,[],[f189,f83])).
% 0.20/0.45  fof(f189,plain,(
% 0.20/0.45    sP6(sK4,sK2,sK3) | ~v1_relat_1(sK3) | ~spl8_10),
% 0.20/0.45    inference(resolution,[],[f108,f50])).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    ( ! [X0,X3,X1] : (~r2_hidden(X3,k10_relat_1(X0,X1)) | sP6(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(equality_resolution,[],[f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 0.20/0.45  fof(f108,plain,(
% 0.20/0.45    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~spl8_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f103])).
% 0.20/0.45  fof(f211,plain,(
% 0.20/0.45    spl8_16 | ~spl8_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f172,f153,f209])).
% 0.20/0.45  fof(f172,plain,(
% 0.20/0.45    r2_hidden(k4_tarski(sK4,sK7(sK3,sK2,sK4)),sK3) | ~spl8_14),
% 0.20/0.45    inference(resolution,[],[f154,f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(k4_tarski(X3,sK7(X0,X1,X3)),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f154,plain,(
% 0.20/0.45    sP6(sK4,sK2,sK3) | ~spl8_14),
% 0.20/0.45    inference(avatar_component_clause,[],[f153])).
% 0.20/0.45  fof(f193,plain,(
% 0.20/0.45    spl8_15 | ~spl8_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f173,f153,f191])).
% 0.20/0.45  fof(f191,plain,(
% 0.20/0.45    spl8_15 <=> r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.45  fof(f173,plain,(
% 0.20/0.45    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl8_14),
% 0.20/0.45    inference(resolution,[],[f154,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(sK7(X0,X1,X3),X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f188,plain,(
% 0.20/0.45    spl8_10 | ~spl8_5 | ~spl8_14),
% 0.20/0.45    inference(avatar_split_clause,[],[f175,f153,f82,f103])).
% 0.20/0.45  fof(f175,plain,(
% 0.20/0.45    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | (~spl8_5 | ~spl8_14)),
% 0.20/0.45    inference(subsumption_resolution,[],[f174,f83])).
% 0.20/0.45  fof(f174,plain,(
% 0.20/0.45    ~v1_relat_1(sK3) | r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~spl8_14),
% 0.20/0.45    inference(resolution,[],[f154,f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | ~v1_relat_1(X0) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 0.20/0.45    inference(equality_resolution,[],[f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f170,plain,(
% 0.20/0.45    spl8_7 | ~spl8_1 | ~spl8_5 | ~spl8_12 | ~spl8_13),
% 0.20/0.45    inference(avatar_split_clause,[],[f162,f137,f119,f82,f58,f89])).
% 0.20/0.45  fof(f89,plain,(
% 0.20/0.45    spl8_7 <=> r2_hidden(sK4,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.45  fof(f119,plain,(
% 0.20/0.45    spl8_12 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.20/0.45  fof(f137,plain,(
% 0.20/0.45    spl8_13 <=> r2_hidden(k4_tarski(sK4,k1_funct_1(sK3,sK4)),sK3)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.45  fof(f162,plain,(
% 0.20/0.45    r2_hidden(sK4,sK0) | (~spl8_1 | ~spl8_5 | ~spl8_12 | ~spl8_13)),
% 0.20/0.45    inference(forward_demodulation,[],[f161,f120])).
% 0.20/0.45  fof(f120,plain,(
% 0.20/0.45    sK0 = k1_relat_1(sK3) | ~spl8_12),
% 0.20/0.45    inference(avatar_component_clause,[],[f119])).
% 0.20/0.45  fof(f161,plain,(
% 0.20/0.45    r2_hidden(sK4,k1_relat_1(sK3)) | (~spl8_1 | ~spl8_5 | ~spl8_13)),
% 0.20/0.45    inference(subsumption_resolution,[],[f143,f83])).
% 0.20/0.45  fof(f143,plain,(
% 0.20/0.45    r2_hidden(sK4,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_13)),
% 0.20/0.45    inference(subsumption_resolution,[],[f141,f59])).
% 0.20/0.45  fof(f141,plain,(
% 0.20/0.45    ~v1_funct_1(sK3) | r2_hidden(sK4,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl8_13),
% 0.20/0.45    inference(resolution,[],[f138,f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f138,plain,(
% 0.20/0.45    r2_hidden(k4_tarski(sK4,k1_funct_1(sK3,sK4)),sK3) | ~spl8_13),
% 0.20/0.45    inference(avatar_component_clause,[],[f137])).
% 0.20/0.45  fof(f160,plain,(
% 0.20/0.45    ~spl8_4 | ~spl8_6 | spl8_10),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f159])).
% 0.20/0.45  fof(f159,plain,(
% 0.20/0.45    $false | (~spl8_4 | ~spl8_6 | spl8_10)),
% 0.20/0.45    inference(subsumption_resolution,[],[f158,f104])).
% 0.20/0.45  fof(f104,plain,(
% 0.20/0.45    ~r2_hidden(sK4,k10_relat_1(sK3,sK2)) | spl8_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f103])).
% 0.20/0.46  fof(f158,plain,(
% 0.20/0.46    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | (~spl8_4 | ~spl8_6)),
% 0.20/0.46    inference(forward_demodulation,[],[f87,f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X0] : (k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)) ) | ~spl8_4),
% 0.20/0.46    inference(resolution,[],[f71,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f70])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    spl8_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f86])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    spl8_6 <=> r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.46  fof(f155,plain,(
% 0.20/0.46    spl8_14 | ~spl8_9 | ~spl8_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f146,f137,f100,f153])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    spl8_9 <=> r2_hidden(k1_funct_1(sK3,sK4),sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.46  fof(f146,plain,(
% 0.20/0.46    sP6(sK4,sK2,sK3) | (~spl8_9 | ~spl8_13)),
% 0.20/0.46    inference(resolution,[],[f140,f112])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~spl8_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f100])).
% 0.20/0.46  fof(f140,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4),X0) | sP6(sK4,X0,sK3)) ) | ~spl8_13),
% 0.20/0.46    inference(resolution,[],[f138,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | sP6(X3,X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    spl8_13 | ~spl8_1 | ~spl8_5 | ~spl8_7 | ~spl8_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f126,f119,f89,f82,f58,f137])).
% 0.20/0.46  fof(f126,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK4,k1_funct_1(sK3,sK4)),sK3) | (~spl8_1 | ~spl8_5 | ~spl8_7 | ~spl8_12)),
% 0.20/0.46    inference(resolution,[],[f125,f90])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    r2_hidden(sK4,sK0) | ~spl8_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f89])).
% 0.20/0.46  fof(f125,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)) ) | (~spl8_1 | ~spl8_5 | ~spl8_12)),
% 0.20/0.46    inference(subsumption_resolution,[],[f124,f83])).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK3) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)) ) | (~spl8_1 | ~spl8_12)),
% 0.20/0.46    inference(subsumption_resolution,[],[f123,f59])).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)) ) | ~spl8_12),
% 0.20/0.46    inference(superposition,[],[f49,f120])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X2,X0] : (~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.20/0.46    inference(equality_resolution,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f122,plain,(
% 0.20/0.46    spl8_12 | ~spl8_8 | ~spl8_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f121,f115,f96,f119])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    spl8_8 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    spl8_11 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    sK0 = k1_relat_1(sK3) | (~spl8_8 | ~spl8_11)),
% 0.20/0.46    inference(forward_demodulation,[],[f116,f97])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f96])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl8_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f115])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    spl8_11 | ~spl8_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f73,f70,f115])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl8_4),
% 0.20/0.46    inference(resolution,[],[f71,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    spl8_9 | ~spl8_4 | spl8_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f111,f103,f70,f100])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    r2_hidden(k1_funct_1(sK3,sK4),sK2) | (~spl8_4 | spl8_10)),
% 0.20/0.46    inference(subsumption_resolution,[],[f110,f104])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~spl8_4),
% 0.20/0.46    inference(forward_demodulation,[],[f24,f76])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    r2_hidden(k1_funct_1(sK3,sK4),sK2) | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : (? [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <~> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : ((? [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <~> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f10])).
% 0.20/0.46  fof(f10,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_2)).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    ~spl8_9 | ~spl8_10 | ~spl8_4 | ~spl8_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f93,f89,f70,f103,f100])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ~r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~r2_hidden(k1_funct_1(sK3,sK4),sK2) | (~spl8_4 | ~spl8_7)),
% 0.20/0.46    inference(forward_demodulation,[],[f92,f76])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ~r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_7),
% 0.20/0.46    inference(subsumption_resolution,[],[f22,f90])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ~r2_hidden(sK4,sK0) | ~r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    spl8_8 | spl8_2 | ~spl8_3 | ~spl8_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f79,f70,f66,f62,f96])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    spl8_2 <=> k1_xboole_0 = sK1),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    spl8_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl8_2 | ~spl8_3 | ~spl8_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f78,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    v1_funct_2(sK3,sK0,sK1) | ~spl8_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f66])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl8_2 | ~spl8_4)),
% 0.20/0.46    inference(subsumption_resolution,[],[f75,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    k1_xboole_0 != sK1 | spl8_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f62])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl8_4),
% 0.20/0.46    inference(resolution,[],[f71,f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(flattening,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    spl8_6 | spl8_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f89,f86])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    r2_hidden(sK4,sK0) | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    spl8_5 | ~spl8_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f80,f70,f82])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    v1_relat_1(sK3) | ~spl8_4),
% 0.20/0.46    inference(subsumption_resolution,[],[f77,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl8_4),
% 0.20/0.46    inference(resolution,[],[f71,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    spl8_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f70])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    spl8_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f66])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ~spl8_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f28,f62])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    k1_xboole_0 != sK1),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    spl8_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f58])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    v1_funct_1(sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (31734)------------------------------
% 0.20/0.46  % (31734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (31734)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (31734)Memory used [KB]: 6268
% 0.20/0.46  % (31734)Time elapsed: 0.059 s
% 0.20/0.46  % (31734)------------------------------
% 0.20/0.46  % (31734)------------------------------
% 0.20/0.46  % (31732)Success in time 0.097 s
%------------------------------------------------------------------------------
