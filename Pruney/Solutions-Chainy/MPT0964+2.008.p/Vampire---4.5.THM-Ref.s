%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 160 expanded)
%              Number of leaves         :   26 (  67 expanded)
%              Depth                    :    6
%              Number of atoms          :  322 ( 547 expanded)
%              Number of equality atoms :   51 (  81 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f80,f84,f88,f96,f106,f124,f131,f145,f163,f175,f179,f185])).

fof(f185,plain,
    ( ~ spl6_2
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_28
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_28
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f55,f144,f67,f174,f178])).

fof(f178,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_relset_1(X1,X0,X2) != X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r2_hidden(X3,X1)
        | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl6_29
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k1_relset_1(X1,X0,X2) != X1
        | ~ r2_hidden(X3,X1)
        | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f174,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl6_28
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f67,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f144,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK2,X0),sK3)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_22
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK2,X0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f55,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f179,plain,(
    spl6_29 ),
    inference(avatar_split_clause,[],[f39,f177])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f175,plain,
    ( spl6_28
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f170,f161,f66,f62,f58,f173])).

fof(f58,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f62,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f161,plain,
    ( spl6_26
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f170,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f169,f63])).

fof(f63,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f169,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl6_3
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f168,f59])).

fof(f59,plain,
    ( k1_xboole_0 != sK1
    | spl6_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f168,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_5
    | ~ spl6_26 ),
    inference(resolution,[],[f162,f67])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f36,f161])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f145,plain,
    ( spl6_22
    | ~ spl6_17
    | ~ spl6_1
    | ~ spl6_10
    | spl6_18 ),
    inference(avatar_split_clause,[],[f141,f122,f86,f50,f119,f143])).

fof(f119,plain,
    ( spl6_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f50,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f86,plain,
    ( spl6_10
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f122,plain,
    ( spl6_18
  <=> r2_hidden(sK2,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(k4_tarski(sK2,X0),sK3) )
    | ~ spl6_1
    | ~ spl6_10
    | spl6_18 ),
    inference(subsumption_resolution,[],[f140,f51])).

fof(f51,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(k4_tarski(sK2,X0),sK3) )
    | ~ spl6_10
    | spl6_18 ),
    inference(resolution,[],[f123,f87])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k1_relat_1(X2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f123,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f122])).

fof(f131,plain,
    ( ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | spl6_17 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | spl6_17 ),
    inference(unit_resulting_resolution,[],[f75,f67,f120,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_8
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f120,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_17 ),
    inference(avatar_component_clause,[],[f119])).

fof(f75,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_7
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f124,plain,
    ( ~ spl6_17
    | ~ spl6_18
    | ~ spl6_1
    | ~ spl6_12
    | spl6_14 ),
    inference(avatar_split_clause,[],[f116,f104,f94,f50,f122,f119])).

fof(f94,plain,
    ( spl6_12
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f104,plain,
    ( spl6_14
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f116,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | ~ spl6_12
    | spl6_14 ),
    inference(subsumption_resolution,[],[f115,f51])).

fof(f115,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_12
    | spl6_14 ),
    inference(resolution,[],[f95,f105])).

fof(f105,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f104])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f106,plain,
    ( ~ spl6_14
    | ~ spl6_5
    | spl6_6
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f102,f82,f70,f66,f104])).

fof(f70,plain,
    ( spl6_6
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f82,plain,
    ( spl6_9
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f102,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl6_5
    | spl6_6
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f71,f101])).

fof(f101,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(resolution,[],[f83,f67])).

fof(f83,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f71,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f96,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f29,f94])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f88,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f84,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f30,f82])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f80,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f27,f78])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f76,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f72,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f68,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f23,f66])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f22,f62])).

fof(f22,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f56,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f52,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (17475)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (17474)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (17483)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (17482)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (17475)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f80,f84,f88,f96,f106,f124,f131,f145,f163,f175,f179,f185])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    ~spl6_2 | ~spl6_5 | ~spl6_22 | ~spl6_28 | ~spl6_29),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f180])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    $false | (~spl6_2 | ~spl6_5 | ~spl6_22 | ~spl6_28 | ~spl6_29)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f55,f144,f67,f174,f178])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k1_relset_1(X1,X0,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) ) | ~spl6_29),
% 0.21/0.47    inference(avatar_component_clause,[],[f177])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    spl6_29 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f173])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    spl6_28 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(sK2,X0),sK3)) ) | ~spl6_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f143])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    spl6_22 <=> ! [X0] : ~r2_hidden(k4_tarski(sK2,X0),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    r2_hidden(sK2,sK0) | ~spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    spl6_2 <=> r2_hidden(sK2,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    spl6_29),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f177])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK5(X2,X3)),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    spl6_28 | spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f170,f161,f66,f62,f58,f173])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl6_3 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl6_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    spl6_26 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_26)),
% 0.21/0.47    inference(subsumption_resolution,[],[f169,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    v1_funct_2(sK3,sK0,sK1) | ~spl6_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl6_3 | ~spl6_5 | ~spl6_26)),
% 0.21/0.47    inference(subsumption_resolution,[],[f168,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    k1_xboole_0 != sK1 | spl6_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (~spl6_5 | ~spl6_26)),
% 0.21/0.47    inference(resolution,[],[f162,f67])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) ) | ~spl6_26),
% 0.21/0.47    inference(avatar_component_clause,[],[f161])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    spl6_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f161])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    spl6_22 | ~spl6_17 | ~spl6_1 | ~spl6_10 | spl6_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f141,f122,f86,f50,f119,f143])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl6_17 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl6_1 <=> v1_funct_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl6_10 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    spl6_18 <=> r2_hidden(sK2,k1_relat_1(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(sK2,X0),sK3)) ) | (~spl6_1 | ~spl6_10 | spl6_18)),
% 0.21/0.47    inference(subsumption_resolution,[],[f140,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    v1_funct_1(sK3) | ~spl6_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~r2_hidden(k4_tarski(sK2,X0),sK3)) ) | (~spl6_10 | spl6_18)),
% 0.21/0.47    inference(resolution,[],[f123,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2)) ) | ~spl6_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f86])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ~r2_hidden(sK2,k1_relat_1(sK3)) | spl6_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f122])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~spl6_5 | ~spl6_7 | ~spl6_8 | spl6_17),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    $false | (~spl6_5 | ~spl6_7 | ~spl6_8 | spl6_17)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f75,f67,f120,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl6_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl6_8 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ~v1_relat_1(sK3) | spl6_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl6_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl6_7 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ~spl6_17 | ~spl6_18 | ~spl6_1 | ~spl6_12 | spl6_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f116,f104,f94,f50,f122,f119])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl6_12 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl6_14 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_1 | ~spl6_12 | spl6_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f115,f51])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ~v1_funct_1(sK3) | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_12 | spl6_14)),
% 0.21/0.47    inference(resolution,[],[f95,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | spl6_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f104])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl6_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f94])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ~spl6_14 | ~spl6_5 | spl6_6 | ~spl6_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f102,f82,f70,f66,f104])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl6_6 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl6_9 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | (~spl6_5 | spl6_6 | ~spl6_9)),
% 0.21/0.47    inference(backward_demodulation,[],[f71,f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | (~spl6_5 | ~spl6_9)),
% 0.21/0.47    inference(resolution,[],[f83,f67])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl6_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f82])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) | spl6_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f70])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl6_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f94])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl6_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f86])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl6_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f82])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl6_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f78])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl6_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f74])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ~spl6_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f70])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl6_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f66])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl6_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f62])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ~spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f58])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl6_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f54])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    r2_hidden(sK2,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl6_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f50])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    v1_funct_1(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (17475)------------------------------
% 0.21/0.47  % (17475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17475)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (17475)Memory used [KB]: 10746
% 0.21/0.47  % (17475)Time elapsed: 0.051 s
% 0.21/0.47  % (17475)------------------------------
% 0.21/0.47  % (17475)------------------------------
% 0.21/0.47  % (17465)Success in time 0.105 s
%------------------------------------------------------------------------------
