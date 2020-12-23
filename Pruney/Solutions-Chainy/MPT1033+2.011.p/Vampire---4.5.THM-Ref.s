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
% DateTime   : Thu Dec  3 13:06:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 305 expanded)
%              Number of leaves         :   40 ( 133 expanded)
%              Depth                    :    9
%              Number of atoms          :  542 (1453 expanded)
%              Number of equality atoms :   67 ( 247 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f379,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f96,f102,f107,f116,f121,f133,f144,f148,f161,f183,f189,f194,f208,f223,f243,f284,f285,f318,f344,f351,f378])).

fof(f378,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | spl6_7
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_20
    | ~ spl6_43 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | spl6_7
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_20
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f360,f132])).

fof(f132,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_15
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f360,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_7
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f83,f356])).

fof(f356,plain,
    ( sK2 = sK3
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f355,f53])).

fof(f53,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f355,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f354,f101])).

fof(f101,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f354,plain,
    ( sK2 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_4
    | ~ spl6_20
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f353,f160])).

fof(f160,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_20
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f353,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | sK2 = sK3
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_4
    | ~ spl6_43 ),
    inference(resolution,[],[f350,f68])).

fof(f68,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_4
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK3)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl6_43
  <=> ! [X0] :
        ( sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ r1_partfun1(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f83,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl6_7
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f351,plain,
    ( spl6_43
    | ~ spl6_11
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f346,f342,f104,f349])).

fof(f104,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f342,plain,
    ( spl6_42
  <=> ! [X1,X0] :
        ( ~ r1_partfun1(X0,sK3)
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f346,plain,
    ( ! [X0] :
        ( sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ r1_partfun1(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_11
    | ~ spl6_42 ),
    inference(resolution,[],[f343,f106])).

fof(f106,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ r1_partfun1(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f342])).

fof(f344,plain,
    ( spl6_42
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f322,f315,f56,f342])).

fof(f56,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f315,plain,
    ( spl6_38
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f322,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(X0,sK3)
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f321,f58])).

fof(f58,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f321,plain,
    ( ! [X0,X1] :
        ( ~ r1_partfun1(X0,sK3)
        | sK3 = X0
        | ~ v1_partfun1(X0,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_38 ),
    inference(resolution,[],[f317,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_partfun1(X3,X0)
      | ~ r1_partfun1(X2,X3)
      | X2 = X3
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f317,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f315])).

fof(f318,plain,
    ( spl6_38
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_18
    | spl6_19 ),
    inference(avatar_split_clause,[],[f313,f154,f146,f104,f76,f315])).

fof(f76,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

% (19277)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f146,plain,
    ( spl6_18
  <=> ! [X3,X2] :
        ( ~ v1_funct_2(sK3,X2,X3)
        | v1_partfun1(sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f154,plain,
    ( spl6_19
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f313,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_18
    | spl6_19 ),
    inference(subsumption_resolution,[],[f312,f155])).

fof(f155,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f312,plain,
    ( v1_partfun1(sK3,sK0)
    | v1_xboole_0(sK1)
    | ~ spl6_6
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f310,f106])).

fof(f310,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ spl6_6
    | ~ spl6_18 ),
    inference(resolution,[],[f147,f78])).

fof(f78,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f147,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK3,X2,X3)
        | v1_partfun1(sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X3) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f285,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != sK2
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f284,plain,
    ( spl6_34
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f225,f220,f281])).

fof(f281,plain,
    ( spl6_34
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f220,plain,
    ( spl6_27
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f225,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_27 ),
    inference(resolution,[],[f222,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f222,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f243,plain,
    ( spl6_28
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f213,f205,f240])).

fof(f240,plain,
    ( spl6_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f205,plain,
    ( spl6_25
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f213,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_25 ),
    inference(resolution,[],[f207,f36])).

fof(f207,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f205])).

fof(f223,plain,
    ( spl6_27
    | ~ spl6_14
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f211,f191,f119,f220])).

fof(f119,plain,
    ( spl6_14
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f191,plain,
    ( spl6_23
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f211,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_14
    | ~ spl6_23 ),
    inference(resolution,[],[f193,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f193,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f191])).

fof(f208,plain,
    ( spl6_25
    | ~ spl6_14
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f203,f186,f119,f205])).

fof(f186,plain,
    ( spl6_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f203,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_14
    | ~ spl6_22 ),
    inference(resolution,[],[f188,f120])).

fof(f188,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f194,plain,
    ( spl6_23
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f176,f113,f104,f191])).

fof(f113,plain,
    ( spl6_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f176,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f172,f47])).

fof(f47,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f172,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f106,f115])).

fof(f115,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f189,plain,
    ( spl6_22
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f175,f113,f99,f186])).

fof(f175,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f171,f47])).

fof(f171,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f101,f115])).

fof(f183,plain,
    ( spl6_12
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f164,f154,f109])).

fof(f109,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f164,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_19 ),
    inference(resolution,[],[f156,f36])).

fof(f156,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f154])).

fof(f161,plain,
    ( spl6_19
    | spl6_20
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f150,f142,f99,f71,f158,f154])).

fof(f71,plain,
    ( spl6_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f142,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f150,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1)
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f149,f101])).

fof(f149,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK1)
    | ~ spl6_5
    | ~ spl6_17 ),
    inference(resolution,[],[f143,f73])).

fof(f73,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f142])).

fof(f148,plain,
    ( spl6_18
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f135,f56,f146])).

fof(f135,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK3,X2,X3)
        | v1_partfun1(sK3,X2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | v1_xboole_0(X3) )
    | ~ spl6_2 ),
    inference(resolution,[],[f39,f58])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f144,plain,
    ( spl6_17
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f134,f51,f142])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f39,f53])).

fof(f133,plain,
    ( spl6_15
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f125,f99,f130])).

fof(f125,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f124,f101])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(subsumption_resolution,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f44,f48_D])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP5(X1,X0) ) ),
    inference(cnf_transformation,[],[f48_D])).

fof(f48_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X1,X2,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    <=> ~ sP5(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f121,plain,
    ( spl6_14
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f117,f93,f119])).

fof(f93,plain,
    ( spl6_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl6_9 ),
    inference(resolution,[],[f37,f95])).

fof(f95,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f116,plain,
    ( ~ spl6_12
    | spl6_13 ),
    inference(avatar_split_clause,[],[f34,f113,f109])).

fof(f34,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_partfun1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ( k1_xboole_0 = sK0
            | k1_xboole_0 != sK1 )
          & r1_partfun1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ( k1_xboole_0 = sK0
          | k1_xboole_0 != sK1 )
        & r1_partfun1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_partfun1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

fof(f107,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f32,f104])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f102,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f29,f99])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,
    ( spl6_9
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f86,f61,f93])).

fof(f61,plain,
    ( spl6_3
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f86,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f63,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_3 ),
    inference(resolution,[],[f36,f63])).

fof(f63,plain,
    ( v1_xboole_0(sK4)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f84,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f35,f81])).

fof(f35,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f31,f76])).

fof(f31,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f33,f66])).

fof(f33,plain,(
    r1_partfun1(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f45,f61])).

fof(f45,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    v1_xboole_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f25])).

fof(f25,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f59,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:00:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (19286)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (19270)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (19291)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (19268)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (19276)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (19271)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (19283)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (19269)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (19270)Refutation not found, incomplete strategy% (19270)------------------------------
% 0.22/0.52  % (19270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19268)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (19278)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (19266)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (19285)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (19275)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (19288)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (19280)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (19270)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19270)Memory used [KB]: 6268
% 0.22/0.53  % (19270)Time elapsed: 0.107 s
% 0.22/0.53  % (19270)------------------------------
% 0.22/0.53  % (19270)------------------------------
% 0.22/0.53  % (19267)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (19287)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (19273)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (19273)Refutation not found, incomplete strategy% (19273)------------------------------
% 0.22/0.53  % (19273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19273)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19273)Memory used [KB]: 1663
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f84,f96,f102,f107,f116,f121,f133,f144,f148,f161,f183,f189,f194,f208,f223,f243,f284,f285,f318,f344,f351,f378])).
% 0.22/0.53  fof(f378,plain,(
% 0.22/0.53    ~spl6_1 | ~spl6_4 | spl6_7 | ~spl6_10 | ~spl6_15 | ~spl6_20 | ~spl6_43),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f377])).
% 0.22/0.54  fof(f377,plain,(
% 0.22/0.54    $false | (~spl6_1 | ~spl6_4 | spl6_7 | ~spl6_10 | ~spl6_15 | ~spl6_20 | ~spl6_43)),
% 0.22/0.54    inference(subsumption_resolution,[],[f360,f132])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl6_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f130])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    spl6_15 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.54  fof(f360,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,sK2,sK2) | (~spl6_1 | ~spl6_4 | spl6_7 | ~spl6_10 | ~spl6_20 | ~spl6_43)),
% 0.22/0.54    inference(backward_demodulation,[],[f83,f356])).
% 0.22/0.54  fof(f356,plain,(
% 0.22/0.54    sK2 = sK3 | (~spl6_1 | ~spl6_4 | ~spl6_10 | ~spl6_20 | ~spl6_43)),
% 0.22/0.54    inference(subsumption_resolution,[],[f355,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    v1_funct_1(sK2) | ~spl6_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    spl6_1 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.54  fof(f355,plain,(
% 0.22/0.54    sK2 = sK3 | ~v1_funct_1(sK2) | (~spl6_4 | ~spl6_10 | ~spl6_20 | ~spl6_43)),
% 0.22/0.54    inference(subsumption_resolution,[],[f354,f101])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f99])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    spl6_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.54  fof(f354,plain,(
% 0.22/0.54    sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl6_4 | ~spl6_20 | ~spl6_43)),
% 0.22/0.54    inference(subsumption_resolution,[],[f353,f160])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    v1_partfun1(sK2,sK0) | ~spl6_20),
% 0.22/0.54    inference(avatar_component_clause,[],[f158])).
% 0.22/0.54  fof(f158,plain,(
% 0.22/0.54    spl6_20 <=> v1_partfun1(sK2,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.54  fof(f353,plain,(
% 0.22/0.54    ~v1_partfun1(sK2,sK0) | sK2 = sK3 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl6_4 | ~spl6_43)),
% 0.22/0.54    inference(resolution,[],[f350,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    r1_partfun1(sK2,sK3) | ~spl6_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    spl6_4 <=> r1_partfun1(sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.54  fof(f350,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_partfun1(X0,sK3) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) ) | ~spl6_43),
% 0.22/0.54    inference(avatar_component_clause,[],[f349])).
% 0.22/0.54  fof(f349,plain,(
% 0.22/0.54    spl6_43 <=> ! [X0] : (sK3 = X0 | ~v1_partfun1(X0,sK0) | ~r1_partfun1(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,sK2,sK3) | spl6_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f81])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    spl6_7 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.54  fof(f351,plain,(
% 0.22/0.54    spl6_43 | ~spl6_11 | ~spl6_42),
% 0.22/0.54    inference(avatar_split_clause,[],[f346,f342,f104,f349])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    spl6_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.54  fof(f342,plain,(
% 0.22/0.54    spl6_42 <=> ! [X1,X0] : (~r1_partfun1(X0,sK3) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.22/0.54  fof(f346,plain,(
% 0.22/0.54    ( ! [X0] : (sK3 = X0 | ~v1_partfun1(X0,sK0) | ~r1_partfun1(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0)) ) | (~spl6_11 | ~spl6_42)),
% 0.22/0.54    inference(resolution,[],[f343,f106])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f104])).
% 0.22/0.54  fof(f343,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~r1_partfun1(X0,sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0)) ) | ~spl6_42),
% 0.22/0.54    inference(avatar_component_clause,[],[f342])).
% 0.22/0.54  fof(f344,plain,(
% 0.22/0.54    spl6_42 | ~spl6_2 | ~spl6_38),
% 0.22/0.54    inference(avatar_split_clause,[],[f322,f315,f56,f342])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    spl6_2 <=> v1_funct_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.54  fof(f315,plain,(
% 0.22/0.54    spl6_38 <=> v1_partfun1(sK3,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.54  fof(f322,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_partfun1(X0,sK3) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0)) ) | (~spl6_2 | ~spl6_38)),
% 0.22/0.54    inference(subsumption_resolution,[],[f321,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    v1_funct_1(sK3) | ~spl6_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f56])).
% 0.22/0.54  fof(f321,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_partfun1(X0,sK3) | sK3 = X0 | ~v1_partfun1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0)) ) | ~spl6_38),
% 0.22/0.54    inference(resolution,[],[f317,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_partfun1(X3,X0) | ~r1_partfun1(X2,X3) | X2 = X3 | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.22/0.54  fof(f317,plain,(
% 0.22/0.54    v1_partfun1(sK3,sK0) | ~spl6_38),
% 0.22/0.54    inference(avatar_component_clause,[],[f315])).
% 0.22/0.54  fof(f318,plain,(
% 0.22/0.54    spl6_38 | ~spl6_6 | ~spl6_11 | ~spl6_18 | spl6_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f313,f154,f146,f104,f76,f315])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl6_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.54  % (19277)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    spl6_18 <=> ! [X3,X2] : (~v1_funct_2(sK3,X2,X3) | v1_partfun1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    spl6_19 <=> v1_xboole_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.54  fof(f313,plain,(
% 0.22/0.54    v1_partfun1(sK3,sK0) | (~spl6_6 | ~spl6_11 | ~spl6_18 | spl6_19)),
% 0.22/0.54    inference(subsumption_resolution,[],[f312,f155])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1) | spl6_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f154])).
% 0.22/0.54  fof(f312,plain,(
% 0.22/0.54    v1_partfun1(sK3,sK0) | v1_xboole_0(sK1) | (~spl6_6 | ~spl6_11 | ~spl6_18)),
% 0.22/0.54    inference(subsumption_resolution,[],[f310,f106])).
% 0.22/0.54  fof(f310,plain,(
% 0.22/0.54    v1_partfun1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | (~spl6_6 | ~spl6_18)),
% 0.22/0.54    inference(resolution,[],[f147,f78])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK0,sK1) | ~spl6_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f76])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~v1_funct_2(sK3,X2,X3) | v1_partfun1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3)) ) | ~spl6_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f146])).
% 0.22/0.54  fof(f285,plain,(
% 0.22/0.54    k1_xboole_0 != sK3 | k1_xboole_0 != sK2 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.22/0.54    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.54  fof(f284,plain,(
% 0.22/0.54    spl6_34 | ~spl6_27),
% 0.22/0.54    inference(avatar_split_clause,[],[f225,f220,f281])).
% 0.22/0.54  fof(f281,plain,(
% 0.22/0.54    spl6_34 <=> k1_xboole_0 = sK3),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.54  fof(f220,plain,(
% 0.22/0.54    spl6_27 <=> v1_xboole_0(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.54  fof(f225,plain,(
% 0.22/0.54    k1_xboole_0 = sK3 | ~spl6_27),
% 0.22/0.54    inference(resolution,[],[f222,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    v1_xboole_0(sK3) | ~spl6_27),
% 0.22/0.54    inference(avatar_component_clause,[],[f220])).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    spl6_28 | ~spl6_25),
% 0.22/0.54    inference(avatar_split_clause,[],[f213,f205,f240])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    spl6_28 <=> k1_xboole_0 = sK2),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    spl6_25 <=> v1_xboole_0(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.54  fof(f213,plain,(
% 0.22/0.54    k1_xboole_0 = sK2 | ~spl6_25),
% 0.22/0.54    inference(resolution,[],[f207,f36])).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    v1_xboole_0(sK2) | ~spl6_25),
% 0.22/0.54    inference(avatar_component_clause,[],[f205])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    spl6_27 | ~spl6_14 | ~spl6_23),
% 0.22/0.54    inference(avatar_split_clause,[],[f211,f191,f119,f220])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    spl6_14 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    spl6_23 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    v1_xboole_0(sK3) | (~spl6_14 | ~spl6_23)),
% 0.22/0.54    inference(resolution,[],[f193,f120])).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl6_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f119])).
% 0.22/0.54  fof(f193,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f191])).
% 0.22/0.54  fof(f208,plain,(
% 0.22/0.54    spl6_25 | ~spl6_14 | ~spl6_22),
% 0.22/0.54    inference(avatar_split_clause,[],[f203,f186,f119,f205])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    spl6_22 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.54  fof(f203,plain,(
% 0.22/0.54    v1_xboole_0(sK2) | (~spl6_14 | ~spl6_22)),
% 0.22/0.54    inference(resolution,[],[f188,f120])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_22),
% 0.22/0.54    inference(avatar_component_clause,[],[f186])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    spl6_23 | ~spl6_11 | ~spl6_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f176,f113,f104,f191])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    spl6_13 <=> k1_xboole_0 = sK0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_11 | ~spl6_13)),
% 0.22/0.54    inference(forward_demodulation,[],[f172,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(flattening,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl6_11 | ~spl6_13)),
% 0.22/0.54    inference(backward_demodulation,[],[f106,f115])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | ~spl6_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f113])).
% 0.22/0.54  fof(f189,plain,(
% 0.22/0.54    spl6_22 | ~spl6_10 | ~spl6_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f175,f113,f99,f186])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_10 | ~spl6_13)),
% 0.22/0.54    inference(forward_demodulation,[],[f171,f47])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl6_10 | ~spl6_13)),
% 0.22/0.54    inference(backward_demodulation,[],[f101,f115])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    spl6_12 | ~spl6_19),
% 0.22/0.54    inference(avatar_split_clause,[],[f164,f154,f109])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    spl6_12 <=> k1_xboole_0 = sK1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | ~spl6_19),
% 0.22/0.54    inference(resolution,[],[f156,f36])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    v1_xboole_0(sK1) | ~spl6_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f154])).
% 0.22/0.54  fof(f161,plain,(
% 0.22/0.54    spl6_19 | spl6_20 | ~spl6_5 | ~spl6_10 | ~spl6_17),
% 0.22/0.54    inference(avatar_split_clause,[],[f150,f142,f99,f71,f158,f154])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    spl6_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    spl6_17 <=> ! [X1,X0] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    v1_partfun1(sK2,sK0) | v1_xboole_0(sK1) | (~spl6_5 | ~spl6_10 | ~spl6_17)),
% 0.22/0.54    inference(subsumption_resolution,[],[f149,f101])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    v1_partfun1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK1) | (~spl6_5 | ~spl6_17)),
% 0.22/0.54    inference(resolution,[],[f143,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    v1_funct_2(sK2,sK0,sK1) | ~spl6_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f71])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl6_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f142])).
% 0.22/0.54  fof(f148,plain,(
% 0.22/0.54    spl6_18 | ~spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f135,f56,f146])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~v1_funct_2(sK3,X2,X3) | v1_partfun1(sK3,X2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_xboole_0(X3)) ) | ~spl6_2),
% 0.22/0.54    inference(resolution,[],[f39,f58])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    spl6_17 | ~spl6_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f134,f51,f142])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl6_1),
% 0.22/0.54    inference(resolution,[],[f39,f53])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    spl6_15 | ~spl6_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f125,f99,f130])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl6_10),
% 0.22/0.54    inference(resolution,[],[f124,f101])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f48,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~sP5(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(general_splitting,[],[f44,f48_D])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP5(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48_D])).
% 0.22/0.54  fof(f48_D,plain,(
% 0.22/0.54    ( ! [X0,X1] : (( ! [X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) <=> ~sP5(X1,X0)) )),
% 0.22/0.54    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    spl6_14 | ~spl6_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f117,f93,f119])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    spl6_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl6_9),
% 0.22/0.54    inference(resolution,[],[f37,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0) | ~spl6_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f93])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    ~spl6_12 | spl6_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f34,f113,f109])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_partfun1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f8])).
% 0.22/0.54  fof(f8,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    spl6_11),
% 0.22/0.54    inference(avatar_split_clause,[],[f32,f104])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    spl6_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f29,f99])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    spl6_9 | ~spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f86,f61,f93])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    spl6_3 <=> v1_xboole_0(sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0) | ~spl6_3),
% 0.22/0.54    inference(backward_demodulation,[],[f63,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    k1_xboole_0 = sK4 | ~spl6_3),
% 0.22/0.54    inference(resolution,[],[f36,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    v1_xboole_0(sK4) | ~spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f61])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ~spl6_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f35,f81])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    spl6_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f31,f76])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    spl6_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f28,f71])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    spl6_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f33,f66])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    r1_partfun1(sK2,sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f61])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    v1_xboole_0(sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    v1_xboole_0(sK4)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK4)),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ? [X0] : v1_xboole_0(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f30,f56])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    spl6_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f27,f51])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (19268)------------------------------
% 0.22/0.54  % (19268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19268)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (19268)Memory used [KB]: 6396
% 0.22/0.54  % (19268)Time elapsed: 0.109 s
% 0.22/0.54  % (19268)------------------------------
% 0.22/0.54  % (19268)------------------------------
% 0.22/0.54  % (19279)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (19262)Success in time 0.175 s
%------------------------------------------------------------------------------
