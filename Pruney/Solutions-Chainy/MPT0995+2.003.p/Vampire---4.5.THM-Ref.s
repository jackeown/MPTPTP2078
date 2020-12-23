%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 169 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  293 ( 605 expanded)
%              Number of equality atoms :   60 ( 128 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f81,f86,f91,f96,f108,f117,f122,f130,f137,f147,f157,f163])).

fof(f163,plain,
    ( ~ spl9_3
    | spl9_14
    | ~ spl9_15 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl9_3
    | spl9_14
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f160,f67])).

fof(f67,plain,
    ( r2_hidden(sK5,sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl9_3
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f160,plain,
    ( ~ r2_hidden(sK5,sK2)
    | spl9_14
    | ~ spl9_15 ),
    inference(resolution,[],[f152,f156])).

fof(f156,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl9_15
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
        | ~ r2_hidden(X0,sK2) )
    | spl9_14 ),
    inference(resolution,[],[f146,f27])).

fof(f27,plain,(
    ! [X4,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f146,plain,
    ( ~ sP7(sK4,sK2,sK3)
    | spl9_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl9_14
  <=> sP7(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f157,plain,
    ( spl9_15
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f150,f124,f105,f83,f60,f55,f154])).

fof(f55,plain,
    ( spl9_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f60,plain,
    ( spl9_2
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f83,plain,
    ( spl9_6
  <=> sK4 = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f105,plain,
    ( spl9_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f124,plain,
    ( spl9_12
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f150,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f149,f62])).

fof(f62,plain,
    ( r2_hidden(sK5,sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f149,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ r2_hidden(sK5,sK0)
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(superposition,[],[f142,f85])).

fof(f85,plain,
    ( sK4 = k1_funct_1(sK3,sK5)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f142,plain,
    ( ! [X4] :
        ( r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3)
        | ~ r2_hidden(X4,sK0) )
    | ~ spl9_1
    | ~ spl9_9
    | ~ spl9_12 ),
    inference(forward_demodulation,[],[f141,f126])).

fof(f126,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f141,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3) )
    | ~ spl9_1
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f76,f107])).

fof(f107,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f76,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(X4,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3) )
    | ~ spl9_1 ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
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

fof(f57,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f147,plain,
    ( ~ spl9_14
    | ~ spl9_9
    | spl9_13 ),
    inference(avatar_split_clause,[],[f140,f134,f105,f144])).

fof(f134,plain,
    ( spl9_13
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f140,plain,
    ( ~ sP7(sK4,sK2,sK3)
    | ~ spl9_9
    | spl9_13 ),
    inference(resolution,[],[f109,f136])).

fof(f136,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl9_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ sP7(X0,X1,sK3) )
    | ~ spl9_9 ),
    inference(resolution,[],[f107,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f137,plain,
    ( ~ spl9_13
    | ~ spl9_7
    | spl9_8 ),
    inference(avatar_split_clause,[],[f129,f93,f88,f134])).

fof(f88,plain,
    ( spl9_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f93,plain,
    ( spl9_8
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f129,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_7
    | spl9_8 ),
    inference(superposition,[],[f95,f97])).

fof(f97,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl9_7 ),
    inference(resolution,[],[f90,f45])).

fof(f45,plain,(
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

fof(f90,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f95,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | spl9_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f130,plain,
    ( spl9_12
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f127,f119,f114,f124])).

fof(f114,plain,
    ( spl9_10
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f119,plain,
    ( spl9_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f127,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl9_10
    | ~ spl9_11 ),
    inference(superposition,[],[f121,f116])).

fof(f116,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f121,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f122,plain,
    ( spl9_11
    | spl9_4
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f103,f88,f78,f70,f119])).

fof(f70,plain,
    ( spl9_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f78,plain,
    ( spl9_5
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f103,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl9_4
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f102,f80])).

fof(f80,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f102,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f99,f72])).

fof(f72,plain,
    ( k1_xboole_0 != sK1
    | spl9_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f99,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl9_7 ),
    inference(resolution,[],[f90,f41])).

fof(f41,plain,(
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

fof(f117,plain,
    ( spl9_10
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f100,f88,f114])).

fof(f100,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_7 ),
    inference(resolution,[],[f90,f35])).

fof(f35,plain,(
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

fof(f108,plain,
    ( spl9_9
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f101,f88,f105])).

fof(f101,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_7 ),
    inference(resolution,[],[f90,f34])).

fof(f34,plain,(
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

fof(f96,plain,(
    ~ spl9_8 ),
    inference(avatar_split_clause,[],[f22,f93])).

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

fof(f91,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f25,f88])).

fof(f25,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f21,f83])).

fof(f21,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f24,f78])).

fof(f24,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f73,plain,(
    ~ spl9_4 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f20,f65])).

fof(f20,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f63,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f19,f60])).

fof(f19,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:55:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (11484)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (11486)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (11495)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (11484)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f164,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f81,f86,f91,f96,f108,f117,f122,f130,f137,f147,f157,f163])).
% 0.22/0.47  fof(f163,plain,(
% 0.22/0.47    ~spl9_3 | spl9_14 | ~spl9_15),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.47  fof(f162,plain,(
% 0.22/0.47    $false | (~spl9_3 | spl9_14 | ~spl9_15)),
% 0.22/0.47    inference(subsumption_resolution,[],[f160,f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    r2_hidden(sK5,sK2) | ~spl9_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    spl9_3 <=> r2_hidden(sK5,sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.47  fof(f160,plain,(
% 0.22/0.47    ~r2_hidden(sK5,sK2) | (spl9_14 | ~spl9_15)),
% 0.22/0.47    inference(resolution,[],[f152,f156])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl9_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f154])).
% 0.22/0.47  fof(f154,plain,(
% 0.22/0.47    spl9_15 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.22/0.47  fof(f152,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK2)) ) | spl9_14),
% 0.22/0.47    inference(resolution,[],[f146,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X4,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.47  fof(f146,plain,(
% 0.22/0.47    ~sP7(sK4,sK2,sK3) | spl9_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f144])).
% 0.22/0.47  fof(f144,plain,(
% 0.22/0.47    spl9_14 <=> sP7(sK4,sK2,sK3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.47  fof(f157,plain,(
% 0.22/0.47    spl9_15 | ~spl9_1 | ~spl9_2 | ~spl9_6 | ~spl9_9 | ~spl9_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f150,f124,f105,f83,f60,f55,f154])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    spl9_1 <=> v1_funct_1(sK3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    spl9_2 <=> r2_hidden(sK5,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    spl9_6 <=> sK4 = k1_funct_1(sK3,sK5)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    spl9_9 <=> v1_relat_1(sK3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    spl9_12 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    r2_hidden(k4_tarski(sK5,sK4),sK3) | (~spl9_1 | ~spl9_2 | ~spl9_6 | ~spl9_9 | ~spl9_12)),
% 0.22/0.47    inference(subsumption_resolution,[],[f149,f62])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    r2_hidden(sK5,sK0) | ~spl9_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f60])).
% 0.22/0.47  fof(f149,plain,(
% 0.22/0.47    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~r2_hidden(sK5,sK0) | (~spl9_1 | ~spl9_6 | ~spl9_9 | ~spl9_12)),
% 0.22/0.47    inference(superposition,[],[f142,f85])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    sK4 = k1_funct_1(sK3,sK5) | ~spl9_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f83])).
% 0.22/0.47  fof(f142,plain,(
% 0.22/0.47    ( ! [X4] : (r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3) | ~r2_hidden(X4,sK0)) ) | (~spl9_1 | ~spl9_9 | ~spl9_12)),
% 0.22/0.47    inference(forward_demodulation,[],[f141,f126])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    sK0 = k1_relat_1(sK3) | ~spl9_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f124])).
% 0.22/0.47  fof(f141,plain,(
% 0.22/0.47    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3)) ) | (~spl9_1 | ~spl9_9)),
% 0.22/0.47    inference(subsumption_resolution,[],[f76,f107])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    v1_relat_1(sK3) | ~spl9_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f105])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X4] : (~v1_relat_1(sK3) | ~r2_hidden(X4,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X4,k1_funct_1(sK3,X4)),sK3)) ) | ~spl9_1),
% 0.22/0.47    inference(resolution,[],[f57,f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X2,X0] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 0.22/0.47    inference(equality_resolution,[],[f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(flattening,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    v1_funct_1(sK3) | ~spl9_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f55])).
% 0.22/0.47  fof(f147,plain,(
% 0.22/0.47    ~spl9_14 | ~spl9_9 | spl9_13),
% 0.22/0.47    inference(avatar_split_clause,[],[f140,f134,f105,f144])).
% 0.22/0.47  fof(f134,plain,(
% 0.22/0.47    spl9_13 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.22/0.47  fof(f140,plain,(
% 0.22/0.47    ~sP7(sK4,sK2,sK3) | (~spl9_9 | spl9_13)),
% 0.22/0.47    inference(resolution,[],[f109,f136])).
% 0.22/0.47  fof(f136,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | spl9_13),
% 0.22/0.47    inference(avatar_component_clause,[],[f134])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(X0,k9_relat_1(sK3,X1)) | ~sP7(X0,X1,sK3)) ) | ~spl9_9),
% 0.22/0.47    inference(resolution,[],[f107,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~sP7(X3,X1,X0) | r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.47    inference(equality_resolution,[],[f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f137,plain,(
% 0.22/0.47    ~spl9_13 | ~spl9_7 | spl9_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f129,f93,f88,f134])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl9_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    spl9_8 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl9_7 | spl9_8)),
% 0.22/0.47    inference(superposition,[],[f95,f97])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl9_7),
% 0.22/0.47    inference(resolution,[],[f90,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f88])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | spl9_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f93])).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    spl9_12 | ~spl9_10 | ~spl9_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f127,f119,f114,f124])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    spl9_10 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    spl9_11 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    sK0 = k1_relat_1(sK3) | (~spl9_10 | ~spl9_11)),
% 0.22/0.47    inference(superposition,[],[f121,f116])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl9_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f114])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl9_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f119])).
% 0.22/0.47  fof(f122,plain,(
% 0.22/0.47    spl9_11 | spl9_4 | ~spl9_5 | ~spl9_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f103,f88,f78,f70,f119])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    spl9_4 <=> k1_xboole_0 = sK1),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    spl9_5 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl9_4 | ~spl9_5 | ~spl9_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f102,f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    v1_funct_2(sK3,sK0,sK1) | ~spl9_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f78])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl9_4 | ~spl9_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f99,f72])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    k1_xboole_0 != sK1 | spl9_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f70])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl9_7),
% 0.22/0.47    inference(resolution,[],[f90,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(flattening,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    spl9_10 | ~spl9_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f100,f88,f114])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl9_7),
% 0.22/0.47    inference(resolution,[],[f90,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    spl9_9 | ~spl9_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f101,f88,f105])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    v1_relat_1(sK3) | ~spl9_7),
% 0.22/0.47    inference(resolution,[],[f90,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    ~spl9_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f93])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_2)).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    spl9_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f88])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    spl9_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f83])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    sK4 = k1_funct_1(sK3,sK5)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl9_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f78])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ~spl9_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f70])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    k1_xboole_0 != sK1),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    spl9_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f20,f65])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    r2_hidden(sK5,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl9_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f19,f60])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    r2_hidden(sK5,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    spl9_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f55])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    v1_funct_1(sK3)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (11484)------------------------------
% 0.22/0.47  % (11484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (11484)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (11484)Memory used [KB]: 10618
% 0.22/0.47  % (11484)Time elapsed: 0.063 s
% 0.22/0.47  % (11484)------------------------------
% 0.22/0.47  % (11484)------------------------------
% 0.22/0.48  % (11478)Success in time 0.119 s
%------------------------------------------------------------------------------
