%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t6_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:49 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 123 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  222 ( 408 expanded)
%              Number of equality atoms :   50 (  80 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f97,f101,f114,f122,f142,f146,f153,f158,f244,f286])).

fof(f286,plain,
    ( ~ spl8_0
    | ~ spl8_16
    | spl8_21
    | ~ spl8_52 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_16
    | ~ spl8_21
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f284,f152])).

fof(f152,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl8_21
  <=> ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f284,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl8_0
    | ~ spl8_16
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f283,f141])).

fof(f141,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_16
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f283,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl8_0
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f281,f92])).

fof(f92,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f281,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl8_52 ),
    inference(resolution,[],[f243,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ sP5(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t6_funct_2.p',d5_funct_1)).

fof(f243,plain,
    ( sP5(k1_funct_1(sK3,sK2),sK3)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl8_52
  <=> sP5(k1_funct_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f244,plain,
    ( spl8_52
    | ~ spl8_2
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f240,f156,f95,f242])).

fof(f95,plain,
    ( spl8_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f156,plain,
    ( spl8_22
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f240,plain,
    ( sP5(k1_funct_1(sK3,sK2),sK3)
    | ~ spl8_2
    | ~ spl8_22 ),
    inference(resolution,[],[f163,f96])).

fof(f96,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sP5(k1_funct_1(sK3,X0),sK3) )
    | ~ spl8_22 ),
    inference(superposition,[],[f84,f157])).

fof(f157,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f156])).

fof(f84,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | sP5(k1_funct_1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP5(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f158,plain,
    ( spl8_22
    | spl8_5
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f137,f120,f112,f99,f156])).

fof(f99,plain,
    ( spl8_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f112,plain,
    ( spl8_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f120,plain,
    ( spl8_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f137,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f131,f136])).

fof(f136,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f135,f113])).

fof(f113,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f135,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_5
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f130,f100])).

fof(f100,plain,
    ( k1_xboole_0 != sK1
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f130,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_12 ),
    inference(resolution,[],[f121,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t6_funct_2.p',d1_funct_2)).

fof(f121,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f131,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_12 ),
    inference(resolution,[],[f121,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t6_funct_2.p',redefinition_k1_relset_1)).

fof(f153,plain,
    ( ~ spl8_21
    | ~ spl8_12
    | spl8_19 ),
    inference(avatar_split_clause,[],[f147,f144,f120,f151])).

fof(f144,plain,
    ( spl8_19
  <=> ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f147,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl8_12
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f145,f128])).

fof(f128,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl8_12 ),
    inference(resolution,[],[f121,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t6_funct_2.p',redefinition_k2_relset_1)).

fof(f145,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,(
    ~ spl8_19 ),
    inference(avatar_split_clause,[],[f54,f144])).

fof(f54,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t6_funct_2.p',t6_funct_2)).

fof(f142,plain,
    ( spl8_16
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f132,f120,f140])).

fof(f132,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_12 ),
    inference(resolution,[],[f121,f80])).

fof(f80,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t6_funct_2.p',cc1_relset_1)).

fof(f122,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f51,f120])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f114,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f50,f112])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f101,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f53,f99])).

fof(f53,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f52,f95])).

fof(f52,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f49,f91])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
