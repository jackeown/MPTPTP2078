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
% DateTime   : Thu Dec  3 13:00:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 148 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  257 ( 447 expanded)
%              Number of equality atoms :   46 (  74 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f65,f69,f83,f87,f91,f96,f102,f107,f126,f129])).

fof(f129,plain,
    ( spl4_5
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl4_5
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f127,f64])).

fof(f64,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_5
  <=> r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f127,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),sK1)
    | ~ spl4_10
    | ~ spl4_16 ),
    inference(resolution,[],[f125,f98])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(X0,sK1) )
    | ~ spl4_10 ),
    inference(resolution,[],[f95,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f95,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_10
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f125,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl4_16
  <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f126,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f122,f104,f81,f51,f47,f124])).

fof(f47,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f51,plain,
    ( spl4_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f81,plain,
    ( spl4_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f104,plain,
    ( spl4_12
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f122,plain,
    ( r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f110,f52])).

fof(f52,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f109,f82])).

fof(f82,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK3)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl4_1
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f108,f48])).

fof(f48,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f108,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) )
    | ~ spl4_12 ),
    inference(superposition,[],[f28,f105])).

fof(f105,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f107,plain,
    ( spl4_12
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f106,f100,f85,f104])).

fof(f85,plain,
    ( spl4_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f100,plain,
    ( spl4_11
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f106,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f101,f86])).

fof(f86,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f101,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f71,f67,f100])).

fof(f67,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f71,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f68,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f96,plain,
    ( spl4_10
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f92,f89,f67,f94])).

fof(f89,plain,
    ( spl4_9
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f92,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f90,f72])).

fof(f72,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f68,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f90,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,
    ( spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f70,f67,f89])).

fof(f70,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl4_6 ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f87,plain,
    ( spl4_8
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f78,f67,f59,f55,f85])).

fof(f55,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f59,plain,
    ( spl4_4
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f78,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f77,f60])).

fof(f60,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f77,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f74,f56])).

fof(f56,plain,
    ( k1_xboole_0 != sK1
    | spl4_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f68,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f83,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f79,f67,f81])).

fof(f79,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f75,f38])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f75,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl4_6 ),
    inference(resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f69,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_hidden(k1_funct_1(X3,X2),X1)
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => ( r2_hidden(k1_funct_1(X3,X2),X1)
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f65,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f59])).

fof(f23,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f53,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f22,f47])).

% (29134)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f22,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:01:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (29136)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (29135)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (29142)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (29128)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (29144)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (29128)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f65,f69,f83,f87,f91,f96,f102,f107,f126,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl4_5 | ~spl4_10 | ~spl4_16),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    $false | (spl4_5 | ~spl4_10 | ~spl4_16)),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK3,sK2),sK1) | spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl4_5 <=> r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK3,sK2),sK1) | (~spl4_10 | ~spl4_16)),
% 0.21/0.49    inference(resolution,[],[f125,f98])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X0,sK1)) ) | ~spl4_10),
% 0.21/0.49    inference(resolution,[],[f95,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl4_10 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl4_16 <=> r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_7 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f122,f104,f81,f51,f47,f124])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl4_1 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl4_2 <=> r2_hidden(sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl4_7 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl4_12 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_7 | ~spl4_12)),
% 0.21/0.49    inference(resolution,[],[f110,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    r2_hidden(sK2,sK0) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f51])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | (~spl4_1 | ~spl4_7 | ~spl4_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | (~spl4_1 | ~spl4_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f108,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    v1_funct_1(sK3) | ~spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f47])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3))) ) | ~spl4_12),
% 0.21/0.49    inference(superposition,[],[f28,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | ~spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl4_12 | ~spl4_8 | ~spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f106,f100,f85,f104])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl4_8 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl4_11 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | (~spl4_8 | ~spl4_11)),
% 0.21/0.49    inference(forward_demodulation,[],[f101,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f100])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl4_11 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f71,f67,f100])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f68,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl4_10 | ~spl4_6 | ~spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f92,f89,f67,f94])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl4_9 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | (~spl4_6 | ~spl4_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f90,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f68,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f89])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    spl4_9 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f70,f67,f89])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f68,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl4_8 | spl4_3 | ~spl4_4 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f67,f59,f55,f85])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl4_3 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl4_4 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | (spl4_3 | ~spl4_4 | ~spl4_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f77,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f59])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | (spl4_3 | ~spl4_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f55])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f68,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl4_7 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f79,f67,f81])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f68,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f67])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (((~r2_hidden(k1_funct_1(X3,X2),X1) & k1_xboole_0 != X1) & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f9])).
% 0.21/0.49  fof(f9,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK3,sK2),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f59])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f55])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f51])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    r2_hidden(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f47])).
% 0.21/0.49  % (29134)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (29128)------------------------------
% 0.21/0.49  % (29128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29128)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (29128)Memory used [KB]: 6140
% 0.21/0.49  % (29128)Time elapsed: 0.066 s
% 0.21/0.49  % (29128)------------------------------
% 0.21/0.49  % (29128)------------------------------
% 0.21/0.49  % (29127)Success in time 0.127 s
%------------------------------------------------------------------------------
