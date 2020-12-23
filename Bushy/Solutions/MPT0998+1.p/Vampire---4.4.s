%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t46_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:46 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 187 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  305 ( 653 expanded)
%              Number of equality atoms :   47 (  97 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f97,f101,f105,f122,f129,f173,f185,f201,f212,f226,f243])).

fof(f243,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f230,f241])).

fof(f241,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f235,f228])).

fof(f228,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_30 ),
    inference(resolution,[],[f200,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(k1_funct_1(X0,X3),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t46_funct_2.p',d13_funct_1)).

fof(f200,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl8_30
  <=> sP6(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f235,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f171,f232])).

fof(f232,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f231,f121])).

fof(f121,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f231,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_0
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f229,f92])).

fof(f92,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f229,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_30 ),
    inference(resolution,[],[f200,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f171,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f49,f106])).

fof(f106,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl8_6 ),
    inference(resolution,[],[f104,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t46_funct_2.p',redefinition_k8_relset_1)).

fof(f104,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f49,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
                & r2_hidden(X4,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
          <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t46_funct_2.p',t46_funct_2)).

fof(f230,plain,
    ( r2_hidden(sK4,sK0)
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f227,f184])).

fof(f184,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl8_24
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f227,plain,
    ( r2_hidden(sK4,k1_relat_1(sK3))
    | ~ spl8_30 ),
    inference(resolution,[],[f200,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f226,plain,
    ( spl8_30
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f220,f183,f210,f127,f199])).

fof(f127,plain,
    ( spl8_12
  <=> r2_hidden(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f210,plain,
    ( spl8_16
  <=> r2_hidden(k1_funct_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f220,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f219,f128])).

fof(f128,plain,
    ( r2_hidden(sK4,sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f219,plain,
    ( ~ r2_hidden(sK4,sK0)
    | sP6(sK4,sK2,sK3)
    | ~ spl8_16
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f213,f184])).

fof(f213,plain,
    ( ~ r2_hidden(sK4,k1_relat_1(sK3))
    | sP6(sK4,sK2,sK3)
    | ~ spl8_16 ),
    inference(resolution,[],[f211,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f211,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f210])).

fof(f212,plain,
    ( spl8_16
    | ~ spl8_6
    | spl8_19 ),
    inference(avatar_split_clause,[],[f161,f147,f103,f210])).

fof(f147,plain,
    ( spl8_19
  <=> ~ r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f161,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_6
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f160,f148])).

fof(f148,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f160,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f51,f106])).

fof(f51,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f201,plain,
    ( spl8_30
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f181,f157,f120,f91,f199])).

fof(f157,plain,
    ( spl8_18
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f181,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_0
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f180,f121])).

fof(f180,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_0
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f174,f92])).

fof(f174,plain,
    ( ~ v1_funct_1(sK3)
    | sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_18 ),
    inference(resolution,[],[f158,f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f158,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f157])).

fof(f185,plain,
    ( spl8_24
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f117,f103,f99,f95,f183])).

fof(f95,plain,
    ( spl8_3
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f99,plain,
    ( spl8_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f117,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f110,f116])).

fof(f116,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f115,f100])).

fof(f100,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f115,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f109,f96])).

fof(f96,plain,
    ( k1_xboole_0 != sK1
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_6 ),
    inference(resolution,[],[f104,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t46_funct_2.p',d1_funct_2)).

fof(f110,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f104,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t46_funct_2.p',redefinition_k1_relset_1)).

fof(f173,plain,
    ( spl8_18
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f168,f124,f103,f157])).

fof(f124,plain,
    ( spl8_10
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f168,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f125,f106])).

fof(f125,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f129,plain,
    ( spl8_10
    | spl8_12 ),
    inference(avatar_split_clause,[],[f50,f127,f124])).

fof(f50,plain,
    ( r2_hidden(sK4,sK0)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f122,plain,
    ( spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f111,f103,f120])).

fof(f111,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f104,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t46_funct_2.p',cc1_relset_1)).

fof(f105,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f54,f103])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f101,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f53,f99])).

fof(f53,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f55,f95])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f52,f91])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
