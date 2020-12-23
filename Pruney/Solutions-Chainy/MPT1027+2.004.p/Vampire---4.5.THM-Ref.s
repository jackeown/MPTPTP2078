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
% DateTime   : Thu Dec  3 13:06:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 164 expanded)
%              Number of leaves         :   23 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  283 ( 491 expanded)
%              Number of equality atoms :   46 (  84 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f71,f77,f82,f92,f103,f110,f119,f132,f141,f150,f155,f163])).

fof(f163,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | spl4_11
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_5
    | spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f161,f131])).

fof(f131,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f161,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_5
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f158,f140])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f158,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(superposition,[],[f156,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

% (4503)Refutation not found, incomplete strategy% (4503)------------------------------
% (4503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | v1_funct_2(sK2,sK0,X0) )
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(resolution,[],[f87,f66])).

% (4503)Termination reason: Refutation not found, incomplete strategy

% (4503)Memory used [KB]: 1663
% (4503)Time elapsed: 0.060 s
% (4503)------------------------------
% (4503)------------------------------
fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(sK2,X0,X1) )
    | ~ spl4_1 ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

% (4505)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f64,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f87,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_5
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f155,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f153,f30])).

fof(f30,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f153,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_xboole_0,X0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f151,f31])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r1_xboole_0(k1_xboole_0,X0) )
    | spl4_13 ),
    inference(resolution,[],[f149,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f149,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_13
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f150,plain,
    ( ~ spl4_13
    | spl4_8
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f143,f138,f107,f147])).

fof(f107,plain,
    ( spl4_8
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f143,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_8
    | ~ spl4_12 ),
    inference(resolution,[],[f112,f140])).

fof(f112,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | spl4_8 ),
    inference(resolution,[],[f109,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f109,plain,
    ( ~ v1_xboole_0(sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f141,plain,
    ( spl4_12
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f127,f116,f74,f138])).

fof(f74,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f116,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f125,f53])).

fof(f125,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(superposition,[],[f76,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f76,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f132,plain,
    ( ~ spl4_11
    | spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f126,f116,f68,f129])).

fof(f68,plain,
    ( spl4_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f126,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | spl4_2
    | ~ spl4_9 ),
    inference(superposition,[],[f70,f118])).

fof(f70,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f119,plain,
    ( spl4_9
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f114,f79,f74,f68,f116])).

fof(f79,plain,
    ( spl4_4
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f114,plain,
    ( k1_xboole_0 = sK1
    | spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f113,f76])).

fof(f113,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f72,f81])).

fof(f81,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f72,plain,
    ( k1_xboole_0 = sK1
    | sK0 != k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_2 ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f110,plain,
    ( ~ spl4_8
    | spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f105,f100,f89,f107])).

fof(f89,plain,
    ( spl4_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f100,plain,
    ( spl4_7
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f105,plain,
    ( ~ v1_xboole_0(sK2)
    | spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f104,f91])).

fof(f91,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f104,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK2)
    | ~ spl4_7 ),
    inference(superposition,[],[f32,f102])).

fof(f102,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f103,plain,
    ( spl4_7
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f95,f79,f74,f100])).

fof(f95,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f93,f76])).

fof(f93,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_4 ),
    inference(superposition,[],[f81,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f92,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f83,f74,f89,f85])).

fof(f83,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_partfun1(sK2,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f82,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & k1_relset_1(X0,X1,X2) = X0
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( k1_relset_1(X0,X1,X2) = X0
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(f77,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f60,f68])).

fof(f60,plain,(
    ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f28,f27,f26])).

fof(f26,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f27,f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:21:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (4493)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (4496)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (4498)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (4493)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (4503)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (4508)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f65,f71,f77,f82,f92,f103,f110,f119,f132,f141,f150,f155,f163])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_5 | spl4_11 | ~spl4_12),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f162])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    $false | (~spl4_1 | ~spl4_5 | spl4_11 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f161,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,sK0,k1_xboole_0) | spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl4_11 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl4_1 | ~spl4_5 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f158,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    spl4_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl4_1 | ~spl4_5)),
% 0.21/0.48    inference(superposition,[],[f156,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  % (4503)Refutation not found, incomplete strategy% (4503)------------------------------
% 0.21/0.48  % (4503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | v1_funct_2(sK2,sK0,X0)) ) | (~spl4_1 | ~spl4_5)),
% 0.21/0.48    inference(resolution,[],[f87,f66])).
% 0.21/0.48  % (4503)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4503)Memory used [KB]: 1663
% 0.21/0.48  % (4503)Time elapsed: 0.060 s
% 0.21/0.48  % (4503)------------------------------
% 0.21/0.48  % (4503)------------------------------
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(sK2,X0,X1)) ) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f64,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  % (4505)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl4_1 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    v1_partfun1(sK2,sK0) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl4_5 <=> v1_partfun1(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    spl4_13),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    $false | spl4_13),
% 0.21/0.48    inference(resolution,[],[f153,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0)) ) | spl4_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f151,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~r1_xboole_0(k1_xboole_0,X0)) ) | spl4_13),
% 0.21/0.48    inference(resolution,[],[f149,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | spl4_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    spl4_13 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~spl4_13 | spl4_8 | ~spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f143,f138,f107,f147])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl4_8 <=> v1_xboole_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | (spl4_8 | ~spl4_12)),
% 0.21/0.48    inference(resolution,[],[f112,f140])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X1)) | ~v1_xboole_0(X1)) ) | spl4_8),
% 0.21/0.48    inference(resolution,[],[f109,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ~v1_xboole_0(sK2) | spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl4_12 | ~spl4_3 | ~spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f127,f116,f74,f138])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl4_9 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_3 | ~spl4_9)),
% 0.21/0.48    inference(forward_demodulation,[],[f125,f53])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl4_3 | ~spl4_9)),
% 0.21/0.48    inference(superposition,[],[f76,f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f116])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ~spl4_11 | spl4_2 | ~spl4_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f126,f116,f68,f129])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl4_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,sK0,k1_xboole_0) | (spl4_2 | ~spl4_9)),
% 0.21/0.48    inference(superposition,[],[f70,f118])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,sK0,sK1) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl4_9 | spl4_2 | ~spl4_3 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f114,f79,f74,f68,f116])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl4_4 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | (spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f76])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl4_2 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f72,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 != k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_2),
% 0.21/0.48    inference(resolution,[],[f70,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~spl4_8 | spl4_6 | ~spl4_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f105,f100,f89,f107])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl4_6 <=> v1_xboole_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl4_7 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~v1_xboole_0(sK2) | (spl4_6 | ~spl4_7)),
% 0.21/0.48    inference(subsumption_resolution,[],[f104,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0) | spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    v1_xboole_0(sK0) | ~v1_xboole_0(sK2) | ~spl4_7),
% 0.21/0.48    inference(superposition,[],[f32,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl4_7 | ~spl4_3 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f95,f79,f74,f100])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | (~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f76])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_4),
% 0.21/0.48    inference(superposition,[],[f81,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl4_5 | ~spl4_6 | ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f83,f74,f89,f85])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~v1_xboole_0(sK0) | v1_partfun1(sK2,sK0) | ~spl4_3),
% 0.21/0.48    inference(resolution,[],[f76,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_partfun1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f79])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & k1_relset_1(X0,X1,X2) = X0) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f74])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f60,f68])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(global_subsumption,[],[f28,f27,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f62])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (4493)------------------------------
% 0.21/0.48  % (4493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4493)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (4493)Memory used [KB]: 10618
% 0.21/0.48  % (4493)Time elapsed: 0.055 s
% 0.21/0.48  % (4493)------------------------------
% 0.21/0.48  % (4493)------------------------------
% 0.21/0.48  % (4489)Success in time 0.118 s
%------------------------------------------------------------------------------
