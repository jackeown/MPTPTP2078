%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0998+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 209 expanded)
%              Number of leaves         :   20 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  346 ( 701 expanded)
%              Number of equality atoms :   51 ( 100 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f65,f70,f85,f91,f97,f103,f108,f115,f125,f133,f137,f145,f151,f157,f162,f166])).

fof(f166,plain,
    ( spl7_6
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl7_6
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(resolution,[],[f161,f95])).

fof(f95,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_8
  <=> sP6(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f161,plain,
    ( ! [X0] : ~ sP6(sK4,X0,sK3)
    | spl7_6
    | ~ spl7_11 ),
    inference(resolution,[],[f83,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ sP6(X0,X1,sK3) )
    | ~ spl7_11 ),
    inference(superposition,[],[f25,f112])).

fof(f112,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_11
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_relat_1(X0))
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f83,plain,
    ( ~ r2_hidden(sK4,sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_6
  <=> r2_hidden(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f162,plain,
    ( spl7_14
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f160,f78,f67,f128])).

fof(f128,plain,
    ( spl7_14
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f67,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f78,plain,
    ( spl7_5
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f160,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f80,f71])).

fof(f71,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl7_4 ),
    inference(resolution,[],[f69,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f80,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f157,plain,
    ( ~ spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f155,f84])).

fof(f84,plain,
    ( r2_hidden(sK4,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f155,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ spl7_7
    | spl7_8
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f154,f112])).

fof(f154,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK3))
    | ~ spl7_7
    | spl7_8 ),
    inference(subsumption_resolution,[],[f153,f90])).

fof(f90,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_7
  <=> r2_hidden(k1_funct_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f153,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,k1_relat_1(sK3))
    | spl7_8 ),
    inference(resolution,[],[f96,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f96,plain,
    ( ~ sP6(sK4,sK2,sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f151,plain,
    ( ~ spl7_8
    | ~ spl7_12
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_12
    | spl7_14 ),
    inference(subsumption_resolution,[],[f149,f95])).

fof(f149,plain,
    ( ~ sP6(sK4,sK2,sK3)
    | ~ spl7_12
    | spl7_14 ),
    inference(resolution,[],[f129,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k10_relat_1(sK3,X1))
        | ~ sP6(X0,X1,sK3) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_12
  <=> ! [X1,X0] :
        ( ~ sP6(X0,X1,sK3)
        | r2_hidden(X0,k10_relat_1(sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f129,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f145,plain,
    ( ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f143,f130])).

fof(f130,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f143,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f142,f71])).

fof(f142,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f138,f90])).

fof(f138,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f17,f84])).

fof(f17,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
                & r2_hidden(X4,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f137,plain,
    ( ~ spl7_1
    | spl7_8
    | ~ spl7_13
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl7_1
    | spl7_8
    | ~ spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f135,f130])).

fof(f135,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl7_1
    | spl7_8
    | ~ spl7_13 ),
    inference(resolution,[],[f134,f96])).

fof(f134,plain,
    ( ! [X2,X3] :
        ( sP6(X2,X3,sK3)
        | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) )
    | ~ spl7_1
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f58,f123])).

fof(f123,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl7_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f58,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK3)
        | sP6(X2,X3,sK3)
        | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f133,plain,
    ( ~ spl7_4
    | spl7_13 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl7_4
    | spl7_13 ),
    inference(resolution,[],[f126,f69])).

fof(f126,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_13 ),
    inference(resolution,[],[f124,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f124,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f125,plain,
    ( spl7_12
    | ~ spl7_13
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f57,f48,f122,f119])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | ~ sP6(X0,X1,sK3)
        | r2_hidden(X0,k10_relat_1(sK3,X1)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f50,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f115,plain,
    ( spl7_11
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f113,f105,f100,f110])).

fof(f100,plain,
    ( spl7_9
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f105,plain,
    ( spl7_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f113,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(superposition,[],[f107,f102])).

fof(f102,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f107,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f105])).

% (2955)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f108,plain,
    ( spl7_10
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f76,f67,f62,f53,f105])).

fof(f53,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f62,plain,
    ( spl7_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f76,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f75,f64])).

fof(f64,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f75,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f73,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK1
    | spl7_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f73,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f69,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f103,plain,
    ( spl7_9
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f74,f67,f100])).

fof(f74,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f69,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f97,plain,
    ( ~ spl7_8
    | spl7_7 ),
    inference(avatar_split_clause,[],[f92,f88,f94])).

fof(f92,plain,
    ( ~ sP6(sK4,sK2,sK3)
    | spl7_7 ),
    inference(resolution,[],[f89,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f91,plain,
    ( spl7_7
    | spl7_5 ),
    inference(avatar_split_clause,[],[f86,f78,f88])).

fof(f86,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | spl7_5 ),
    inference(subsumption_resolution,[],[f19,f79])).

fof(f79,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f19,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f18,f82,f78])).

fof(f18,plain,
    ( r2_hidden(sK4,sK0)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f22,f67])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f65,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f21,f62])).

fof(f21,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f56,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f20,f48])).

fof(f20,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
