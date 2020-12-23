%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 156 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  275 ( 490 expanded)
%              Number of equality atoms :   63 (  98 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f77,f82,f95,f100,f105,f112,f119,f125,f140,f144,f152,f159])).

fof(f159,plain,
    ( ~ spl7_2
    | ~ spl7_9
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_9
    | spl7_15 ),
    inference(subsumption_resolution,[],[f157,f62])).

fof(f62,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f157,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl7_2
    | ~ spl7_9
    | spl7_15 ),
    inference(forward_demodulation,[],[f156,f109])).

fof(f109,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl7_9
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f156,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ spl7_2
    | spl7_15 ),
    inference(subsumption_resolution,[],[f154,f62])).

fof(f154,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | spl7_15 ),
    inference(resolution,[],[f151,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( sP5(k1_funct_1(X0,X4),X1,X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f151,plain,
    ( ~ sP5(k1_funct_1(sK3,sK2),sK0,sK3)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl7_15
  <=> sP5(k1_funct_1(sK3,sK2),sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f152,plain,
    ( ~ spl7_15
    | spl7_11
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f145,f134,f122,f149])).

fof(f122,plain,
    ( spl7_11
  <=> r2_hidden(k1_funct_1(sK3,sK2),k9_relat_1(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f134,plain,
    ( spl7_13
  <=> ! [X1,X0] :
        ( ~ sP5(X0,X1,sK3)
        | r2_hidden(X0,k9_relat_1(sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f145,plain,
    ( ~ sP5(k1_funct_1(sK3,sK2),sK0,sK3)
    | spl7_11
    | ~ spl7_13 ),
    inference(resolution,[],[f135,f124])).

fof(f124,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k9_relat_1(sK3,sK0))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ sP5(X0,X1,sK3) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f144,plain,
    ( ~ spl7_5
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl7_5
    | spl7_14 ),
    inference(subsumption_resolution,[],[f142,f35])).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f142,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_5
    | spl7_14 ),
    inference(resolution,[],[f141,f81])).

fof(f81,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_14 ),
    inference(resolution,[],[f139,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f139,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl7_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f140,plain,
    ( spl7_13
    | ~ spl7_14
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f69,f55,f137,f134])).

fof(f55,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | ~ sP5(X0,X1,sK3)
        | r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f57,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP5(X3,X1,X0)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f125,plain,
    ( ~ spl7_11
    | spl7_6
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f120,f116,f92,f122])).

fof(f92,plain,
    ( spl7_6
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f116,plain,
    ( spl7_10
  <=> k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f120,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k9_relat_1(sK3,sK0))
    | spl7_6
    | ~ spl7_10 ),
    inference(superposition,[],[f94,f118])).

fof(f118,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f94,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f119,plain,
    ( spl7_10
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f114,f79,f116])).

fof(f114,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0)
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f86,f83])).

fof(f83,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl7_5 ),
    inference(resolution,[],[f81,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f86,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k7_relset_1(sK0,sK1,sK3,sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f81,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f112,plain,
    ( spl7_9
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f110,f102,f97,f107])).

fof(f97,plain,
    ( spl7_7
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f102,plain,
    ( spl7_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f110,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(superposition,[],[f104,f99])).

fof(f99,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f104,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f105,plain,
    ( spl7_8
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f90,f79,f74,f65,f102])).

fof(f65,plain,
    ( spl7_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f74,plain,
    ( spl7_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f90,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f89,f76])).

fof(f76,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f89,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f85,f67])).

fof(f67,plain,
    ( k1_xboole_0 != sK1
    | spl7_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f81,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f100,plain,
    ( spl7_7
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f88,f79,f97])).

fof(f88,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f81,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f95,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f25,f92])).

fof(f25,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f82,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f22,f79])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f21,f74])).

fof(f21,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f24,f65])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f23,f60])).

fof(f23,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f20,f55])).

fof(f20,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 15:09:55 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.42  % (7730)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.42  % (7730)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f160,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f58,f63,f68,f77,f82,f95,f100,f105,f112,f119,f125,f140,f144,f152,f159])).
% 0.20/0.42  fof(f159,plain,(
% 0.20/0.42    ~spl7_2 | ~spl7_9 | spl7_15),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.42  fof(f158,plain,(
% 0.20/0.42    $false | (~spl7_2 | ~spl7_9 | spl7_15)),
% 0.20/0.42    inference(subsumption_resolution,[],[f157,f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    r2_hidden(sK2,sK0) | ~spl7_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f60])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    spl7_2 <=> r2_hidden(sK2,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.42  fof(f157,plain,(
% 0.20/0.42    ~r2_hidden(sK2,sK0) | (~spl7_2 | ~spl7_9 | spl7_15)),
% 0.20/0.42    inference(forward_demodulation,[],[f156,f109])).
% 0.20/0.42  fof(f109,plain,(
% 0.20/0.42    sK0 = k1_relat_1(sK3) | ~spl7_9),
% 0.20/0.42    inference(avatar_component_clause,[],[f107])).
% 0.20/0.42  fof(f107,plain,(
% 0.20/0.42    spl7_9 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.42  fof(f156,plain,(
% 0.20/0.42    ~r2_hidden(sK2,k1_relat_1(sK3)) | (~spl7_2 | spl7_15)),
% 0.20/0.42    inference(subsumption_resolution,[],[f154,f62])).
% 0.20/0.42  fof(f154,plain,(
% 0.20/0.42    ~r2_hidden(sK2,sK0) | ~r2_hidden(sK2,k1_relat_1(sK3)) | spl7_15),
% 0.20/0.42    inference(resolution,[],[f151,f48])).
% 0.20/0.42  fof(f48,plain,(
% 0.20/0.42    ( ! [X4,X0,X1] : (sP5(k1_funct_1(X0,X4),X1,X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) )),
% 0.20/0.42    inference(equality_resolution,[],[f27])).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    ( ! [X4,X0,X3,X1] : (~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X1) | k1_funct_1(X0,X4) != X3 | sP5(X3,X1,X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(flattening,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.20/0.42  fof(f151,plain,(
% 0.20/0.42    ~sP5(k1_funct_1(sK3,sK2),sK0,sK3) | spl7_15),
% 0.20/0.42    inference(avatar_component_clause,[],[f149])).
% 0.20/0.42  fof(f149,plain,(
% 0.20/0.42    spl7_15 <=> sP5(k1_funct_1(sK3,sK2),sK0,sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.42  fof(f152,plain,(
% 0.20/0.42    ~spl7_15 | spl7_11 | ~spl7_13),
% 0.20/0.42    inference(avatar_split_clause,[],[f145,f134,f122,f149])).
% 0.20/0.42  fof(f122,plain,(
% 0.20/0.42    spl7_11 <=> r2_hidden(k1_funct_1(sK3,sK2),k9_relat_1(sK3,sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.42  fof(f134,plain,(
% 0.20/0.42    spl7_13 <=> ! [X1,X0] : (~sP5(X0,X1,sK3) | r2_hidden(X0,k9_relat_1(sK3,X1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.42  fof(f145,plain,(
% 0.20/0.42    ~sP5(k1_funct_1(sK3,sK2),sK0,sK3) | (spl7_11 | ~spl7_13)),
% 0.20/0.42    inference(resolution,[],[f135,f124])).
% 0.20/0.42  fof(f124,plain,(
% 0.20/0.42    ~r2_hidden(k1_funct_1(sK3,sK2),k9_relat_1(sK3,sK0)) | spl7_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f122])).
% 0.20/0.42  fof(f135,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r2_hidden(X0,k9_relat_1(sK3,X1)) | ~sP5(X0,X1,sK3)) ) | ~spl7_13),
% 0.20/0.42    inference(avatar_component_clause,[],[f134])).
% 0.20/0.42  fof(f144,plain,(
% 0.20/0.42    ~spl7_5 | spl7_14),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f143])).
% 0.20/0.42  fof(f143,plain,(
% 0.20/0.42    $false | (~spl7_5 | spl7_14)),
% 0.20/0.42    inference(subsumption_resolution,[],[f142,f35])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.42  fof(f142,plain,(
% 0.20/0.42    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_5 | spl7_14)),
% 0.20/0.42    inference(resolution,[],[f141,f81])).
% 0.20/0.42  fof(f81,plain,(
% 0.20/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f79])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    spl7_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.42  fof(f141,plain,(
% 0.20/0.42    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_14),
% 0.20/0.42    inference(resolution,[],[f139,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.42  fof(f139,plain,(
% 0.20/0.42    ~v1_relat_1(sK3) | spl7_14),
% 0.20/0.42    inference(avatar_component_clause,[],[f137])).
% 0.20/0.42  fof(f137,plain,(
% 0.20/0.42    spl7_14 <=> v1_relat_1(sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.42  fof(f140,plain,(
% 0.20/0.42    spl7_13 | ~spl7_14 | ~spl7_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f69,f55,f137,f134])).
% 0.20/0.42  fof(f55,plain,(
% 0.20/0.42    spl7_1 <=> v1_funct_1(sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.42  fof(f69,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~v1_relat_1(sK3) | ~sP5(X0,X1,sK3) | r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl7_1),
% 0.20/0.42    inference(resolution,[],[f57,f47])).
% 0.20/0.42  fof(f47,plain,(
% 0.20/0.42    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~sP5(X3,X1,X0) | r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.20/0.42    inference(equality_resolution,[],[f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    v1_funct_1(sK3) | ~spl7_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f55])).
% 0.20/0.42  fof(f125,plain,(
% 0.20/0.42    ~spl7_11 | spl7_6 | ~spl7_10),
% 0.20/0.42    inference(avatar_split_clause,[],[f120,f116,f92,f122])).
% 0.20/0.42  fof(f92,plain,(
% 0.20/0.42    spl7_6 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.42  fof(f116,plain,(
% 0.20/0.42    spl7_10 <=> k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.42  fof(f120,plain,(
% 0.20/0.42    ~r2_hidden(k1_funct_1(sK3,sK2),k9_relat_1(sK3,sK0)) | (spl7_6 | ~spl7_10)),
% 0.20/0.42    inference(superposition,[],[f94,f118])).
% 0.20/0.42  fof(f118,plain,(
% 0.20/0.42    k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0) | ~spl7_10),
% 0.20/0.42    inference(avatar_component_clause,[],[f116])).
% 0.20/0.42  fof(f94,plain,(
% 0.20/0.42    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | spl7_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f92])).
% 0.20/0.42  fof(f119,plain,(
% 0.20/0.42    spl7_10 | ~spl7_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f114,f79,f116])).
% 0.20/0.42  fof(f114,plain,(
% 0.20/0.42    k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0) | ~spl7_5),
% 0.20/0.42    inference(forward_demodulation,[],[f86,f83])).
% 0.20/0.42  fof(f83,plain,(
% 0.20/0.42    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl7_5),
% 0.20/0.42    inference(resolution,[],[f81,f45])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f19])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.42  fof(f86,plain,(
% 0.20/0.42    k2_relset_1(sK0,sK1,sK3) = k7_relset_1(sK0,sK1,sK3,sK0) | ~spl7_5),
% 0.20/0.42    inference(resolution,[],[f81,f37])).
% 0.20/0.42  fof(f37,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f16])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.42  fof(f112,plain,(
% 0.20/0.42    spl7_9 | ~spl7_7 | ~spl7_8),
% 0.20/0.42    inference(avatar_split_clause,[],[f110,f102,f97,f107])).
% 0.20/0.42  fof(f97,plain,(
% 0.20/0.42    spl7_7 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.42  fof(f102,plain,(
% 0.20/0.42    spl7_8 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.42  fof(f110,plain,(
% 0.20/0.42    sK0 = k1_relat_1(sK3) | (~spl7_7 | ~spl7_8)),
% 0.20/0.42    inference(superposition,[],[f104,f99])).
% 0.20/0.42  fof(f99,plain,(
% 0.20/0.42    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl7_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f97])).
% 0.20/0.42  fof(f104,plain,(
% 0.20/0.42    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f102])).
% 0.20/0.42  fof(f105,plain,(
% 0.20/0.42    spl7_8 | spl7_3 | ~spl7_4 | ~spl7_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f90,f79,f74,f65,f102])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl7_3 <=> k1_xboole_0 = sK1),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.42  fof(f74,plain,(
% 0.20/0.42    spl7_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.42  fof(f90,plain,(
% 0.20/0.42    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.42    inference(subsumption_resolution,[],[f89,f76])).
% 0.20/0.42  fof(f76,plain,(
% 0.20/0.42    v1_funct_2(sK3,sK0,sK1) | ~spl7_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f74])).
% 0.20/0.42  fof(f89,plain,(
% 0.20/0.42    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl7_3 | ~spl7_5)),
% 0.20/0.42    inference(subsumption_resolution,[],[f85,f67])).
% 0.20/0.42  fof(f67,plain,(
% 0.20/0.42    k1_xboole_0 != sK1 | spl7_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f65])).
% 0.20/0.42  fof(f85,plain,(
% 0.20/0.42    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl7_5),
% 0.20/0.42    inference(resolution,[],[f81,f44])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f18])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(flattening,[],[f17])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.42  fof(f100,plain,(
% 0.20/0.42    spl7_7 | ~spl7_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f88,f79,f97])).
% 0.20/0.42  fof(f88,plain,(
% 0.20/0.42    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl7_5),
% 0.20/0.42    inference(resolution,[],[f81,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.42    inference(ennf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.42  fof(f95,plain,(
% 0.20/0.42    ~spl7_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f25,f92])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 0.20/0.42  fof(f82,plain,(
% 0.20/0.42    spl7_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f22,f79])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f77,plain,(
% 0.20/0.42    spl7_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f21,f74])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f68,plain,(
% 0.20/0.42    ~spl7_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f24,f65])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    k1_xboole_0 != sK1),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f63,plain,(
% 0.20/0.42    spl7_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f23,f60])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    r2_hidden(sK2,sK0)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    spl7_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f20,f55])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    v1_funct_1(sK3)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (7730)------------------------------
% 0.20/0.42  % (7730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (7730)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (7730)Memory used [KB]: 10618
% 0.20/0.42  % (7730)Time elapsed: 0.008 s
% 0.20/0.42  % (7730)------------------------------
% 0.20/0.42  % (7730)------------------------------
% 0.20/0.43  % (7726)Success in time 0.063 s
%------------------------------------------------------------------------------
