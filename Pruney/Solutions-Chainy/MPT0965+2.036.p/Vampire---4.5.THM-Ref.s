%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 198 expanded)
%              Number of leaves         :   34 (  85 expanded)
%              Depth                    :    6
%              Number of atoms          :  407 ( 673 expanded)
%              Number of equality atoms :   52 (  85 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f72,f76,f80,f84,f92,f96,f100,f108,f113,f126,f141,f161,f164,f173,f177,f184,f202,f207,f215,f221,f226])).

fof(f226,plain,
    ( ~ spl6_2
    | spl6_5
    | ~ spl6_37 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | ~ spl6_2
    | spl6_5
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f223,f59])).

fof(f59,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f223,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl6_5
    | ~ spl6_37 ),
    inference(resolution,[],[f214,f71])).

fof(f71,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_5
  <=> r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f214,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl6_37
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f221,plain,
    ( spl6_3
    | ~ spl6_10
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl6_3
    | ~ spl6_10
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f218,f63])).

fof(f63,plain,
    ( k1_xboole_0 != sK1
    | spl6_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f218,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_10
    | ~ spl6_36 ),
    inference(resolution,[],[f211,f91])).

fof(f91,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_10
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK5(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f211,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK1)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl6_36
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f215,plain,
    ( spl6_36
    | spl6_37
    | ~ spl6_15
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f208,f205,f111,f213,f210])).

fof(f111,plain,
    ( spl6_15
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f205,plain,
    ( spl6_35
  <=> ! [X0] :
        ( m1_subset_1(k1_funct_1(sK3,X0),sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),sK1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_15
    | ~ spl6_35 ),
    inference(resolution,[],[f206,f112])).

fof(f112,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X2,X1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f111])).

fof(f206,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_funct_1(sK3,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f205])).

fof(f207,plain,
    ( spl6_35
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f203,f200,f74,f205])).

fof(f74,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f200,plain,
    ( spl6_34
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,sK0)
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f203,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_funct_1(sK3,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_6
    | ~ spl6_34 ),
    inference(resolution,[],[f201,f75])).

fof(f75,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f201,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( spl6_34
    | ~ spl6_6
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f188,f182,f175,f124,f74,f200])).

fof(f124,plain,
    ( spl6_18
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f175,plain,
    ( spl6_30
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f182,plain,
    ( spl6_31
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl6_6
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_31 ),
    inference(backward_demodulation,[],[f176,f187])).

fof(f187,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_6
    | ~ spl6_18
    | ~ spl6_31 ),
    inference(subsumption_resolution,[],[f185,f75])).

fof(f185,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_18
    | ~ spl6_31 ),
    inference(superposition,[],[f183,f125])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f124])).

fof(f183,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f182])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f175])).

fof(f184,plain,
    ( spl6_31
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f180,f171,f74,f66,f62,f182])).

fof(f66,plain,
    ( spl6_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f171,plain,
    ( spl6_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f180,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f179,f67])).

fof(f67,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f179,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl6_3
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f178,f63])).

fof(f178,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(resolution,[],[f172,f75])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f171])).

fof(f177,plain,
    ( spl6_30
    | ~ spl6_14
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f169,f159,f106,f175])).

fof(f106,plain,
    ( spl6_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f159,plain,
    ( spl6_27
  <=> ! [X1,X0] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ r2_hidden(X1,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f169,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl6_14
    | ~ spl6_27 ),
    inference(resolution,[],[f160,f107])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f106])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ r2_hidden(X1,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X1),X0) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f159])).

fof(f173,plain,(
    spl6_29 ),
    inference(avatar_split_clause,[],[f46,f171])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f164,plain,
    ( ~ spl6_6
    | ~ spl6_7
    | ~ spl6_11
    | spl6_26 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_11
    | spl6_26 ),
    inference(unit_resulting_resolution,[],[f79,f75,f157,f95])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f157,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_26
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f79,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_7
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f161,plain,
    ( ~ spl6_26
    | spl6_27
    | ~ spl6_1
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f154,f139,f54,f159,f156])).

fof(f54,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f139,plain,
    ( spl6_22
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v5_relat_1(X2,X0)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X1,k1_relat_1(X2))
        | m1_subset_1(k1_funct_1(X2,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(X1,k1_relat_1(sK3))
        | m1_subset_1(k1_funct_1(sK3,X1),X0) )
    | ~ spl6_1
    | ~ spl6_22 ),
    inference(resolution,[],[f140,f55])).

fof(f55,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v5_relat_1(X2,X0)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X1,k1_relat_1(X2))
        | m1_subset_1(k1_funct_1(X2,X1),X0) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f141,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f47,f139])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | m1_subset_1(k1_funct_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f126,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f38,f124])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f113,plain,
    ( spl6_15
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f109,f98,f82,f111])).

fof(f82,plain,
    ( spl6_8
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f98,plain,
    ( spl6_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X2,X1) )
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(resolution,[],[f99,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1)
        | r2_hidden(X0,X1) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f108,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f40,f106])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f100,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f37,f98])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f96,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f30,f94])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f92,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f35,f90])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f84,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f80,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f36,f78])).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f76,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f26,f74])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f72,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f25,f66])).

fof(f25,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f64,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f24,f54])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:44:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (1136)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (1142)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (1142)Refutation not found, incomplete strategy% (1142)------------------------------
% 0.21/0.48  % (1142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1136)Refutation not found, incomplete strategy% (1136)------------------------------
% 0.21/0.48  % (1136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1136)Memory used [KB]: 6140
% 0.21/0.48  % (1136)Time elapsed: 0.071 s
% 0.21/0.48  % (1136)------------------------------
% 0.21/0.48  % (1136)------------------------------
% 0.21/0.48  % (1142)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (1142)Memory used [KB]: 1663
% 0.21/0.48  % (1142)Time elapsed: 0.066 s
% 0.21/0.48  % (1142)------------------------------
% 0.21/0.48  % (1142)------------------------------
% 0.21/0.49  % (1129)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (1125)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (1125)Refutation not found, incomplete strategy% (1125)------------------------------
% 0.21/0.49  % (1125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1125)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1125)Memory used [KB]: 10618
% 0.21/0.49  % (1125)Time elapsed: 0.080 s
% 0.21/0.49  % (1125)------------------------------
% 0.21/0.49  % (1125)------------------------------
% 0.21/0.49  % (1131)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (1133)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (1133)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f72,f76,f80,f84,f92,f96,f100,f108,f113,f126,f141,f161,f164,f173,f177,f184,f202,f207,f215,f221,f226])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    ~spl6_2 | spl6_5 | ~spl6_37),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f225])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    $false | (~spl6_2 | spl6_5 | ~spl6_37)),
% 0.21/0.50    inference(subsumption_resolution,[],[f223,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    r2_hidden(sK2,sK0) | ~spl6_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl6_2 <=> r2_hidden(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ~r2_hidden(sK2,sK0) | (spl6_5 | ~spl6_37)),
% 0.21/0.50    inference(resolution,[],[f214,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) | spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl6_5 <=> r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f213])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl6_37 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    spl6_3 | ~spl6_10 | ~spl6_36),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    $false | (spl6_3 | ~spl6_10 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f218,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    k1_xboole_0 != sK1 | spl6_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl6_3 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | (~spl6_10 | ~spl6_36)),
% 0.21/0.50    inference(resolution,[],[f211,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) ) | ~spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl6_10 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.50  fof(f211,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,sK1)) ) | ~spl6_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f210])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    spl6_36 <=> ! [X1] : ~r2_hidden(X1,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    spl6_36 | spl6_37 | ~spl6_15 | ~spl6_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f208,f205,f111,f213,f210])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl6_15 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | ~r2_hidden(X2,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    spl6_35 <=> ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),sK1) | ~r2_hidden(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),sK1) | ~r2_hidden(X1,sK1)) ) | (~spl6_15 | ~spl6_35)),
% 0.21/0.50    inference(resolution,[],[f206,f112])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | ~r2_hidden(X2,X1)) ) | ~spl6_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f111])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),sK1) | ~r2_hidden(X0,sK0)) ) | ~spl6_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f205])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    spl6_35 | ~spl6_6 | ~spl6_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f203,f200,f74,f205])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    spl6_34 <=> ! [X1,X0,X2] : (~r2_hidden(X0,sK0) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_funct_1(sK3,X0),sK1) | ~r2_hidden(X0,sK0)) ) | (~spl6_6 | ~spl6_34)),
% 0.21/0.50    inference(resolution,[],[f201,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f74])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,sK0)) ) | ~spl6_34),
% 0.21/0.50    inference(avatar_component_clause,[],[f200])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl6_34 | ~spl6_6 | ~spl6_18 | ~spl6_30 | ~spl6_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f188,f182,f175,f124,f74,f200])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl6_18 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    spl6_30 <=> ! [X1,X0,X2] : (~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    spl6_31 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK0) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | (~spl6_6 | ~spl6_18 | ~spl6_30 | ~spl6_31)),
% 0.21/0.50    inference(backward_demodulation,[],[f176,f187])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | (~spl6_6 | ~spl6_18 | ~spl6_31)),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f75])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_18 | ~spl6_31)),
% 0.21/0.50    inference(superposition,[],[f183,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f124])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f182])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | ~spl6_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f175])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    spl6_31 | spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f180,f171,f74,f66,f62,f182])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl6_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    spl6_29 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f179,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl6_3 | ~spl6_6 | ~spl6_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f178,f63])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (~spl6_6 | ~spl6_29)),
% 0.21/0.50    inference(resolution,[],[f172,f75])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) ) | ~spl6_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f171])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    spl6_30 | ~spl6_14 | ~spl6_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f169,f159,f106,f175])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl6_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl6_27 <=> ! [X1,X0] : (~v5_relat_1(sK3,X0) | ~r2_hidden(X1,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X1),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | (~spl6_14 | ~spl6_27)),
% 0.21/0.50    inference(resolution,[],[f160,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | ~r2_hidden(X1,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X1),X0)) ) | ~spl6_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f159])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    spl6_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f171])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ~spl6_6 | ~spl6_7 | ~spl6_11 | spl6_26),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    $false | (~spl6_6 | ~spl6_7 | ~spl6_11 | spl6_26)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f79,f75,f157,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl6_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl6_11 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl6_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl6_26 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl6_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl6_7 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~spl6_26 | spl6_27 | ~spl6_1 | ~spl6_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f154,f139,f54,f159,f156])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl6_1 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    spl6_22 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v5_relat_1(X2,X0) | ~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3) | ~r2_hidden(X1,k1_relat_1(sK3)) | m1_subset_1(k1_funct_1(sK3,X1),X0)) ) | (~spl6_1 | ~spl6_22)),
% 0.21/0.50    inference(resolution,[],[f140,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f54])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0)) ) | ~spl6_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f139])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl6_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f139])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v5_relat_1(X2,X0) | ~v1_funct_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | m1_subset_1(k1_funct_1(X2,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl6_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f124])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl6_15 | ~spl6_8 | ~spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f109,f98,f82,f111])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl6_8 <=> ! [X1,X0] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl6_12 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,X1) | ~r2_hidden(X2,X1)) ) | (~spl6_8 | ~spl6_12)),
% 0.21/0.50    inference(resolution,[],[f99,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) ) | ~spl6_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) ) | ~spl6_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl6_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f106])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f98])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl6_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f94])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl6_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f90])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f82])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f78])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f74])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f70])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f66])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ~spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f62])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    k1_xboole_0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f58])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    r2_hidden(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f54])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1133)------------------------------
% 0.21/0.50  % (1133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1133)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1133)Memory used [KB]: 10746
% 0.21/0.50  % (1133)Time elapsed: 0.085 s
% 0.21/0.50  % (1133)------------------------------
% 0.21/0.50  % (1133)------------------------------
% 0.21/0.50  % (1139)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (1134)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (1121)Success in time 0.139 s
%------------------------------------------------------------------------------
