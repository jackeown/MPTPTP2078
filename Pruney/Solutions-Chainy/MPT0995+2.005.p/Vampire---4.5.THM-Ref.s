%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 175 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  320 ( 647 expanded)
%              Number of equality atoms :   57 ( 130 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f76,f81,f86,f91,f103,f111,f116,f124,f133,f144,f155])).

fof(f155,plain,
    ( ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | spl7_13
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12
    | spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f152,f62])).

fof(f62,plain,
    ( r2_hidden(sK5,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_3
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f152,plain,
    ( ~ r2_hidden(sK5,sK2)
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12
    | spl7_13
    | ~ spl7_14 ),
    inference(resolution,[],[f151,f132])).

fof(f132,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_13
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f151,plain,
    ( ! [X0] :
        ( r2_hidden(sK4,k9_relat_1(sK3,X0))
        | ~ r2_hidden(sK5,X0) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(resolution,[],[f150,f143])).

fof(f143,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl7_14
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f150,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,X5),sK3)
        | ~ r2_hidden(X4,X6)
        | r2_hidden(X5,k9_relat_1(sK3,X6)) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f149,f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK3)
        | r2_hidden(X0,sK0) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f127,f120])).

fof(f120,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_12
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) )
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f69,f102])).

fof(f102,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK3)
        | r2_hidden(X0,k1_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(X0,X1),sK3) )
    | ~ spl7_1 ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f52,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f149,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(k4_tarski(X4,X5),sK3)
        | ~ r2_hidden(X4,X6)
        | r2_hidden(X5,k9_relat_1(sK3,X6)) )
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f106,f120])).

fof(f106,plain,
    ( ! [X6,X4,X5] :
        ( ~ r2_hidden(X4,k1_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(X4,X5),sK3)
        | ~ r2_hidden(X4,X6)
        | r2_hidden(X5,k9_relat_1(sK3,X6)) )
    | ~ spl7_9 ),
    inference(resolution,[],[f102,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f144,plain,
    ( spl7_14
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f139,f118,f100,f78,f55,f50,f141])).

fof(f55,plain,
    ( spl7_2
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f78,plain,
    ( spl7_6
  <=> sK4 = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f139,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f138,f80])).

fof(f80,plain,
    ( sK4 = k1_funct_1(sK3,sK5)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f138,plain,
    ( r2_hidden(k4_tarski(sK5,k1_funct_1(sK3,sK5)),sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(resolution,[],[f136,f57])).

fof(f57,plain,
    ( r2_hidden(sK5,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f136,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3) )
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f135,f120])).

fof(f135,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3) )
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f71,f102])).

fof(f71,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(X4,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3) )
    | ~ spl7_1 ),
    inference(resolution,[],[f52,f48])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f133,plain,
    ( ~ spl7_13
    | ~ spl7_7
    | spl7_8 ),
    inference(avatar_split_clause,[],[f123,f88,f83,f130])).

fof(f83,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f88,plain,
    ( spl7_8
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f123,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl7_7
    | spl7_8 ),
    inference(superposition,[],[f90,f92])).

fof(f92,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl7_7 ),
    inference(resolution,[],[f85,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f85,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f90,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f124,plain,
    ( spl7_12
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f121,f113,f108,f118])).

fof(f108,plain,
    ( spl7_10
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f113,plain,
    ( spl7_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f121,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(superposition,[],[f115,f110])).

fof(f110,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f115,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f116,plain,
    ( spl7_11
    | spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f98,f83,f73,f65,f113])).

fof(f65,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f73,plain,
    ( spl7_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f98,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f97,f75])).

fof(f75,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f97,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f94,f67])).

fof(f67,plain,
    ( k1_xboole_0 != sK1
    | spl7_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f94,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f85,f38])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f111,plain,
    ( spl7_10
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f95,f83,f108])).

fof(f95,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f85,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f103,plain,
    ( spl7_9
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f96,f83,f100])).

fof(f96,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f85,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f91,plain,(
    ~ spl7_8 ),
    inference(avatar_split_clause,[],[f22,f88])).

fof(f22,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).

fof(f86,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f25,f83])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f21,f78])).

fof(f21,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f24,f73])).

fof(f24,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f20,f60])).

fof(f20,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f19,f55])).

fof(f19,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f53,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:25:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.42  % (4613)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.46  % (4608)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (4608)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f156,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f76,f81,f86,f91,f103,f111,f116,f124,f133,f144,f155])).
% 0.20/0.46  fof(f155,plain,(
% 0.20/0.46    ~spl7_1 | ~spl7_3 | ~spl7_9 | ~spl7_12 | spl7_13 | ~spl7_14),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.46  fof(f154,plain,(
% 0.20/0.46    $false | (~spl7_1 | ~spl7_3 | ~spl7_9 | ~spl7_12 | spl7_13 | ~spl7_14)),
% 0.20/0.46    inference(subsumption_resolution,[],[f152,f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    r2_hidden(sK5,sK2) | ~spl7_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    spl7_3 <=> r2_hidden(sK5,sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    ~r2_hidden(sK5,sK2) | (~spl7_1 | ~spl7_9 | ~spl7_12 | spl7_13 | ~spl7_14)),
% 0.20/0.46    inference(resolution,[],[f151,f132])).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | spl7_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f130])).
% 0.20/0.46  fof(f130,plain,(
% 0.20/0.46    spl7_13 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK4,k9_relat_1(sK3,X0)) | ~r2_hidden(sK5,X0)) ) | (~spl7_1 | ~spl7_9 | ~spl7_12 | ~spl7_14)),
% 0.20/0.46    inference(resolution,[],[f150,f143])).
% 0.20/0.46  fof(f143,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl7_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f141])).
% 0.20/0.46  fof(f141,plain,(
% 0.20/0.46    spl7_14 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.46  fof(f150,plain,(
% 0.20/0.46    ( ! [X6,X4,X5] : (~r2_hidden(k4_tarski(X4,X5),sK3) | ~r2_hidden(X4,X6) | r2_hidden(X5,k9_relat_1(sK3,X6))) ) | (~spl7_1 | ~spl7_9 | ~spl7_12)),
% 0.20/0.46    inference(subsumption_resolution,[],[f149,f128])).
% 0.20/0.46  fof(f128,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK3) | r2_hidden(X0,sK0)) ) | (~spl7_1 | ~spl7_9 | ~spl7_12)),
% 0.20/0.46    inference(forward_demodulation,[],[f127,f120])).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    sK0 = k1_relat_1(sK3) | ~spl7_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f118])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    spl7_12 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.46  fof(f127,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(k4_tarski(X0,X1),sK3)) ) | (~spl7_1 | ~spl7_9)),
% 0.20/0.46    inference(subsumption_resolution,[],[f69,f102])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    v1_relat_1(sK3) | ~spl7_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f100])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    spl7_9 <=> v1_relat_1(sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(sK3) | r2_hidden(X0,k1_relat_1(sK3)) | ~r2_hidden(k4_tarski(X0,X1),sK3)) ) | ~spl7_1),
% 0.20/0.46    inference(resolution,[],[f52,f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.46    inference(flattening,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    v1_funct_1(sK3) | ~spl7_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    spl7_1 <=> v1_funct_1(sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.46  fof(f149,plain,(
% 0.20/0.46    ( ! [X6,X4,X5] : (~r2_hidden(X4,sK0) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~r2_hidden(X4,X6) | r2_hidden(X5,k9_relat_1(sK3,X6))) ) | (~spl7_9 | ~spl7_12)),
% 0.20/0.46    inference(forward_demodulation,[],[f106,f120])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    ( ! [X6,X4,X5] : (~r2_hidden(X4,k1_relat_1(sK3)) | ~r2_hidden(k4_tarski(X4,X5),sK3) | ~r2_hidden(X4,X6) | r2_hidden(X5,k9_relat_1(sK3,X6))) ) | ~spl7_9),
% 0.20/0.46    inference(resolution,[],[f102,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.46  fof(f144,plain,(
% 0.20/0.46    spl7_14 | ~spl7_1 | ~spl7_2 | ~spl7_6 | ~spl7_9 | ~spl7_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f139,f118,f100,f78,f55,f50,f141])).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl7_2 <=> r2_hidden(sK5,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    spl7_6 <=> sK4 = k1_funct_1(sK3,sK5)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK5,sK4),sK3) | (~spl7_1 | ~spl7_2 | ~spl7_6 | ~spl7_9 | ~spl7_12)),
% 0.20/0.46    inference(forward_demodulation,[],[f138,f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    sK4 = k1_funct_1(sK3,sK5) | ~spl7_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f78])).
% 0.20/0.46  fof(f138,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK5,k1_funct_1(sK3,sK5)),sK3) | (~spl7_1 | ~spl7_2 | ~spl7_9 | ~spl7_12)),
% 0.20/0.46    inference(resolution,[],[f136,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    r2_hidden(sK5,sK0) | ~spl7_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f55])).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    ( ! [X4] : (~r2_hidden(X4,sK0) | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3)) ) | (~spl7_1 | ~spl7_9 | ~spl7_12)),
% 0.20/0.46    inference(forward_demodulation,[],[f135,f120])).
% 0.20/0.46  fof(f135,plain,(
% 0.20/0.46    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3)) ) | (~spl7_1 | ~spl7_9)),
% 0.20/0.46    inference(subsumption_resolution,[],[f71,f102])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ( ! [X4] : (~v1_relat_1(sK3) | ~r2_hidden(X4,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3)) ) | ~spl7_1),
% 0.20/0.46    inference(resolution,[],[f52,f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ( ! [X2,X0] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.20/0.46    inference(equality_resolution,[],[f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f133,plain,(
% 0.20/0.46    ~spl7_13 | ~spl7_7 | spl7_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f123,f88,f83,f130])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    spl7_8 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl7_7 | spl7_8)),
% 0.20/0.46    inference(superposition,[],[f90,f92])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl7_7),
% 0.20/0.46    inference(resolution,[],[f85,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f83])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | spl7_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f88])).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    spl7_12 | ~spl7_10 | ~spl7_11),
% 0.20/0.46    inference(avatar_split_clause,[],[f121,f113,f108,f118])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    spl7_10 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    spl7_11 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    sK0 = k1_relat_1(sK3) | (~spl7_10 | ~spl7_11)),
% 0.20/0.46    inference(superposition,[],[f115,f110])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f108])).
% 0.20/0.46  fof(f115,plain,(
% 0.20/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f113])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    spl7_11 | spl7_4 | ~spl7_5 | ~spl7_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f98,f83,f73,f65,f113])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    spl7_4 <=> k1_xboole_0 = sK1),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    spl7_5 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl7_4 | ~spl7_5 | ~spl7_7)),
% 0.20/0.46    inference(subsumption_resolution,[],[f97,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    v1_funct_2(sK3,sK0,sK1) | ~spl7_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f73])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl7_4 | ~spl7_7)),
% 0.20/0.46    inference(subsumption_resolution,[],[f94,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    k1_xboole_0 != sK1 | spl7_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f65])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl7_7),
% 0.20/0.46    inference(resolution,[],[f85,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(flattening,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    spl7_10 | ~spl7_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f95,f83,f108])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_7),
% 0.20/0.46    inference(resolution,[],[f85,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    spl7_9 | ~spl7_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f96,f83,f100])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    v1_relat_1(sK3) | ~spl7_7),
% 0.20/0.46    inference(resolution,[],[f85,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ~spl7_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f88])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    spl7_7),
% 0.20/0.46    inference(avatar_split_clause,[],[f25,f83])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    spl7_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f78])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    sK4 = k1_funct_1(sK3,sK5)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    spl7_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f73])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ~spl7_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f65])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    k1_xboole_0 != sK1),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl7_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f60])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    r2_hidden(sK5,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    spl7_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f55])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    r2_hidden(sK5,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl7_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f50])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    v1_funct_1(sK3)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (4608)------------------------------
% 0.20/0.46  % (4608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (4608)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (4608)Memory used [KB]: 10618
% 0.20/0.46  % (4608)Time elapsed: 0.059 s
% 0.20/0.46  % (4608)------------------------------
% 0.20/0.46  % (4608)------------------------------
% 0.20/0.46  % (4610)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (4623)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (4604)Success in time 0.122 s
%------------------------------------------------------------------------------
