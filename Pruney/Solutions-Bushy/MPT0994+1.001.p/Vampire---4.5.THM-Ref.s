%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0994+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:02 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 156 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :  307 ( 671 expanded)
%              Number of equality atoms :   74 ( 169 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f73,f77,f83,f90,f98,f110,f117,f131,f140])).

fof(f140,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_8
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f138,f129,f115,f81,f63,f59])).

fof(f59,plain,
    ( spl5_3
  <=> r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f63,plain,
    ( spl5_4
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f81,plain,
    ( spl5_8
  <=> k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f115,plain,
    ( spl5_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f129,plain,
    ( spl5_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | ~ r2_hidden(k1_funct_1(sK4,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f138,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    | ~ spl5_4
    | spl5_8
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(sK4,sK2)
    | ~ r2_hidden(k1_funct_1(sK4,sK2),sK3)
    | ~ spl5_4
    | spl5_8
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(superposition,[],[f82,f133])).

fof(f133,plain,
    ( ! [X0] :
        ( k1_funct_1(sK4,sK2) = k1_funct_1(k8_relat_1(X0,sK4),sK2)
        | ~ r2_hidden(k1_funct_1(sK4,sK2),X0) )
    | ~ spl5_4
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(resolution,[],[f132,f64])).

fof(f64,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k1_funct_1(sK4,X0),X1)
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) )
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(resolution,[],[f130,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k1_funct_1(sK4,X0),X1) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f129])).

fof(f82,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f131,plain,
    ( ~ spl5_11
    | spl5_15
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f127,f95,f75,f129,f101])).

fof(f101,plain,
    ( spl5_11
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f75,plain,
    ( spl5_7
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f95,plain,
    ( spl5_10
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k1_funct_1(sK4,X0),X1)
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | ~ v1_relat_1(sK4) )
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f126,f96])).

fof(f96,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f95])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK4,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | ~ v1_relat_1(sK4) )
    | ~ spl5_7 ),
    inference(resolution,[],[f43,f76])).

fof(f76,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f117,plain,
    ( ~ spl5_11
    | spl5_13
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f113,f75,f115,f101])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,sK4)))
        | k1_funct_1(sK4,X0) = k1_funct_1(k8_relat_1(X1,sK4),X0)
        | ~ v1_relat_1(sK4) )
    | ~ spl5_7 ),
    inference(resolution,[],[f40,f76])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(f110,plain,
    ( ~ spl5_5
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl5_5
    | spl5_11 ),
    inference(subsumption_resolution,[],[f68,f108])).

fof(f108,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_11 ),
    inference(resolution,[],[f102,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f102,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f68,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f98,plain,
    ( ~ spl5_5
    | spl5_10
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f92,f86,f95,f67])).

fof(f86,plain,
    ( spl5_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f92,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_9 ),
    inference(superposition,[],[f33,f87])).

fof(f87,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK4)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f90,plain,
    ( spl5_9
    | spl5_2
    | ~ spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f84,f67,f71,f55,f86])).

fof(f55,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f71,plain,
    ( spl5_6
  <=> v1_funct_2(sK4,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f84,plain,
    ( ~ v1_funct_2(sK4,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f34,f68])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f83,plain,
    ( ~ spl5_8
    | spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f79,f67,f51,f81])).

fof(f51,plain,
    ( spl5_1
  <=> k1_funct_1(sK4,sK2) = k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f79,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k8_relat_1(sK3,sK4),sK2)
    | spl5_1
    | ~ spl5_5 ),
    inference(superposition,[],[f52,f78])).

fof(f78,plain,
    ( ! [X0] : k6_relset_1(sK0,sK1,X0,sK4) = k8_relat_1(X0,sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f44,f68])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k6_relset_1(X0,X1,X2,X3) = k8_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_relset_1)).

fof(f52,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f77,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f25,f75])).

fof(f25,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

% (29747)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f21,plain,
    ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
    & k1_xboole_0 != sK1
    & r2_hidden(k1_funct_1(sK4,sK2),sK3)
    & r2_hidden(sK2,sK0)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK4,sK0,sK1)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
        & k1_xboole_0 != X1
        & r2_hidden(k1_funct_1(X4,X2),X3)
        & r2_hidden(X2,X0)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
   => ( k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2)
      & k1_xboole_0 != sK1
      & r2_hidden(k1_funct_1(sK4,sK2),sK3)
      & r2_hidden(sK2,sK0)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK4,sK0,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k1_funct_1(X4,X2) != k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
      & k1_xboole_0 != X1
      & r2_hidden(k1_funct_1(X4,X2),X3)
      & r2_hidden(X2,X0)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X4,X0,X1)
      & v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X4,X0,X1)
          & v1_funct_1(X4) )
       => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
            & r2_hidden(X2,X0) )
         => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4) )
     => ( ( r2_hidden(k1_funct_1(X4,X2),X3)
          & r2_hidden(X2,X0) )
       => ( k1_funct_1(X4,X2) = k1_funct_1(k6_relset_1(X0,X1,X3,X4),X2)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_funct_2)).

fof(f73,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f26,f71])).

fof(f26,plain,(
    v1_funct_2(sK4,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f28,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    r2_hidden(k1_funct_1(sK4,sK2),sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f31,f51])).

fof(f31,plain,(
    k1_funct_1(sK4,sK2) != k1_funct_1(k6_relset_1(sK0,sK1,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
