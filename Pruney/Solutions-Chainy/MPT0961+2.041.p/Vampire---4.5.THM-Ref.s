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
% DateTime   : Thu Dec  3 13:00:16 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 169 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  324 ( 578 expanded)
%              Number of equality atoms :  101 ( 175 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f234,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f80,f90,f97,f183,f190,f209,f215,f233])).

fof(f233,plain,
    ( ~ spl1_6
    | ~ spl1_7
    | ~ spl1_11
    | spl1_12 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl1_6
    | ~ spl1_7
    | ~ spl1_11
    | spl1_12 ),
    inference(subsumption_resolution,[],[f231,f116])).

fof(f116,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl1_6
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f115,f96])).

fof(f96,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl1_7
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl1_6 ),
    inference(trivial_inequality_removal,[],[f114])).

fof(f114,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl1_6 ),
    inference(superposition,[],[f113,f89])).

fof(f89,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f87])).

% (4505)Refutation not found, incomplete strategy% (4505)------------------------------
% (4505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f87,plain,
    ( spl1_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

% (4505)Termination reason: Refutation not found, incomplete strategy

% (4505)Memory used [KB]: 1663
% (4505)Time elapsed: 0.140 s
% (4505)------------------------------
% (4505)------------------------------
fof(f113,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f111,f59])).

fof(f59,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f110,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f110,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f56,f59])).

fof(f56,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f16])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f231,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_6
    | ~ spl1_11
    | spl1_12 ),
    inference(forward_demodulation,[],[f230,f89])).

fof(f230,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl1_11
    | spl1_12 ),
    inference(forward_demodulation,[],[f214,f208])).

fof(f208,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl1_11
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f214,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_12 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl1_12
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f215,plain,
    ( ~ spl1_12
    | spl1_2
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f210,f180,f67,f212])).

fof(f67,plain,
    ( spl1_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f180,plain,
    ( spl1_8
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f210,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_2
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f69,f182])).

fof(f182,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f180])).

fof(f69,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f209,plain,
    ( spl1_11
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f204,f180,f77,f206])).

fof(f77,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f204,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_4
    | ~ spl1_8 ),
    inference(subsumption_resolution,[],[f193,f79])).

fof(f79,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f193,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl1_8 ),
    inference(trivial_inequality_removal,[],[f192])).

% (4482)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f192,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | ~ v1_relat_1(sK0)
    | ~ spl1_8 ),
    inference(superposition,[],[f45,f182])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f190,plain,
    ( spl1_3
    | ~ spl1_4 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl1_3
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f188,f79])).

fof(f188,plain,
    ( ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f187,f60])).

% (4475)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f187,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(subsumption_resolution,[],[f185,f60])).

fof(f185,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_3 ),
    inference(resolution,[],[f73,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f73,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl1_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl1_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f183,plain,
    ( spl1_8
    | spl1_2
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f178,f77,f67,f180])).

fof(f178,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | spl1_2
    | ~ spl1_4 ),
    inference(subsumption_resolution,[],[f177,f79])).

fof(f177,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(subsumption_resolution,[],[f174,f60])).

fof(f174,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl1_2 ),
    inference(resolution,[],[f146,f69])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f143,f60])).

fof(f143,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ r1_tarski(k1_relat_1(X1),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f142,f39])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1) ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f34,f38])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f92,f94])).

fof(f92,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f91,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f91,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f40,f51])).

fof(f51,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f40,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f90,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f46,f87])).

fof(f46,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f80,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f75,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f63,plain,
    ( spl1_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f31,f71,f67,f63])).

fof(f31,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (4481)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.51  % (4476)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.20/0.51  % (4476)Refutation not found, incomplete strategy% (4476)------------------------------
% 1.20/0.51  % (4476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (4476)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.51  
% 1.20/0.51  % (4476)Memory used [KB]: 1663
% 1.20/0.51  % (4476)Time elapsed: 0.108 s
% 1.20/0.51  % (4476)------------------------------
% 1.20/0.51  % (4476)------------------------------
% 1.20/0.52  % (4496)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.20/0.52  % (4484)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.20/0.52  % (4489)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.20/0.52  % (4491)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.20/0.52  % (4496)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % (4495)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.20/0.53  % (4477)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.20/0.53  % (4498)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.20/0.53  % (4490)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.20/0.53  % (4487)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.20/0.53  % (4499)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.33/0.53  % (4487)Refutation not found, incomplete strategy% (4487)------------------------------
% 1.33/0.53  % (4487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (4487)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (4487)Memory used [KB]: 10618
% 1.33/0.53  % (4487)Time elapsed: 0.124 s
% 1.33/0.53  % (4487)------------------------------
% 1.33/0.53  % (4487)------------------------------
% 1.33/0.53  % (4499)Refutation not found, incomplete strategy% (4499)------------------------------
% 1.33/0.53  % (4499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (4499)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (4499)Memory used [KB]: 10618
% 1.33/0.53  % (4499)Time elapsed: 0.128 s
% 1.33/0.53  % (4499)------------------------------
% 1.33/0.53  % (4499)------------------------------
% 1.33/0.53  % (4505)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.33/0.53  % (4478)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.53  % (4480)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.53  % SZS output start Proof for theBenchmark
% 1.33/0.53  fof(f234,plain,(
% 1.33/0.53    $false),
% 1.33/0.53    inference(avatar_sat_refutation,[],[f74,f75,f80,f90,f97,f183,f190,f209,f215,f233])).
% 1.33/0.53  fof(f233,plain,(
% 1.33/0.53    ~spl1_6 | ~spl1_7 | ~spl1_11 | spl1_12),
% 1.33/0.53    inference(avatar_contradiction_clause,[],[f232])).
% 1.33/0.53  fof(f232,plain,(
% 1.33/0.53    $false | (~spl1_6 | ~spl1_7 | ~spl1_11 | spl1_12)),
% 1.33/0.53    inference(subsumption_resolution,[],[f231,f116])).
% 1.33/0.53  fof(f116,plain,(
% 1.33/0.53    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl1_6 | ~spl1_7)),
% 1.33/0.53    inference(subsumption_resolution,[],[f115,f96])).
% 1.33/0.53  fof(f96,plain,(
% 1.33/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl1_7),
% 1.33/0.53    inference(avatar_component_clause,[],[f94])).
% 1.33/0.53  fof(f94,plain,(
% 1.33/0.53    spl1_7 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 1.33/0.53  fof(f115,plain,(
% 1.33/0.53    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl1_6),
% 1.33/0.53    inference(trivial_inequality_removal,[],[f114])).
% 1.33/0.53  fof(f114,plain,(
% 1.33/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl1_6),
% 1.33/0.53    inference(superposition,[],[f113,f89])).
% 1.33/0.53  fof(f89,plain,(
% 1.33/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_6),
% 1.33/0.53    inference(avatar_component_clause,[],[f87])).
% 1.33/0.53  % (4505)Refutation not found, incomplete strategy% (4505)------------------------------
% 1.33/0.53  % (4505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  fof(f87,plain,(
% 1.33/0.53    spl1_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.33/0.53  % (4505)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (4505)Memory used [KB]: 1663
% 1.33/0.53  % (4505)Time elapsed: 0.140 s
% 1.33/0.53  % (4505)------------------------------
% 1.33/0.53  % (4505)------------------------------
% 1.33/0.53  fof(f113,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 1.33/0.53    inference(duplicate_literal_removal,[],[f112])).
% 1.33/0.53  fof(f112,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 1.33/0.53    inference(forward_demodulation,[],[f111,f59])).
% 1.33/0.53  fof(f59,plain,(
% 1.33/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.33/0.53    inference(equality_resolution,[],[f42])).
% 1.33/0.53  fof(f42,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.33/0.53    inference(cnf_transformation,[],[f26])).
% 1.33/0.53  fof(f26,plain,(
% 1.33/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.33/0.53    inference(flattening,[],[f25])).
% 1.33/0.53  fof(f25,plain,(
% 1.33/0.53    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.33/0.53    inference(nnf_transformation,[],[f3])).
% 1.33/0.53  fof(f3,axiom,(
% 1.33/0.53    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.33/0.53  fof(f111,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 1.33/0.53    inference(superposition,[],[f110,f38])).
% 1.33/0.53  fof(f38,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f17])).
% 1.33/0.53  fof(f17,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.53    inference(ennf_transformation,[],[f8])).
% 1.33/0.53  fof(f8,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.33/0.53  fof(f110,plain,(
% 1.33/0.53    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 1.33/0.53    inference(forward_demodulation,[],[f56,f59])).
% 1.33/0.53  fof(f56,plain,(
% 1.33/0.53    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.33/0.53    inference(equality_resolution,[],[f35])).
% 1.33/0.53  fof(f35,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f24])).
% 1.33/0.53  fof(f24,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.53    inference(nnf_transformation,[],[f16])).
% 1.33/0.53  fof(f16,plain,(
% 1.33/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.53    inference(flattening,[],[f15])).
% 1.33/0.53  fof(f15,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.33/0.53    inference(ennf_transformation,[],[f10])).
% 1.33/0.53  fof(f10,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.33/0.53  fof(f231,plain,(
% 1.33/0.53    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl1_6 | ~spl1_11 | spl1_12)),
% 1.33/0.53    inference(forward_demodulation,[],[f230,f89])).
% 1.33/0.53  fof(f230,plain,(
% 1.33/0.53    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl1_11 | spl1_12)),
% 1.33/0.53    inference(forward_demodulation,[],[f214,f208])).
% 1.33/0.53  fof(f208,plain,(
% 1.33/0.53    k1_xboole_0 = sK0 | ~spl1_11),
% 1.33/0.53    inference(avatar_component_clause,[],[f206])).
% 1.33/0.53  fof(f206,plain,(
% 1.33/0.53    spl1_11 <=> k1_xboole_0 = sK0),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 1.33/0.53  fof(f214,plain,(
% 1.33/0.53    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | spl1_12),
% 1.33/0.53    inference(avatar_component_clause,[],[f212])).
% 1.33/0.53  fof(f212,plain,(
% 1.33/0.53    spl1_12 <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 1.33/0.53  fof(f215,plain,(
% 1.33/0.53    ~spl1_12 | spl1_2 | ~spl1_8),
% 1.33/0.53    inference(avatar_split_clause,[],[f210,f180,f67,f212])).
% 1.33/0.53  fof(f67,plain,(
% 1.33/0.53    spl1_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.33/0.53  fof(f180,plain,(
% 1.33/0.53    spl1_8 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 1.33/0.53  fof(f210,plain,(
% 1.33/0.53    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl1_2 | ~spl1_8)),
% 1.33/0.53    inference(forward_demodulation,[],[f69,f182])).
% 1.33/0.53  fof(f182,plain,(
% 1.33/0.53    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_8),
% 1.33/0.53    inference(avatar_component_clause,[],[f180])).
% 1.33/0.53  fof(f69,plain,(
% 1.33/0.53    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_2),
% 1.33/0.53    inference(avatar_component_clause,[],[f67])).
% 1.33/0.53  fof(f209,plain,(
% 1.33/0.53    spl1_11 | ~spl1_4 | ~spl1_8),
% 1.33/0.53    inference(avatar_split_clause,[],[f204,f180,f77,f206])).
% 1.33/0.53  fof(f77,plain,(
% 1.33/0.53    spl1_4 <=> v1_relat_1(sK0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.33/0.53  fof(f204,plain,(
% 1.33/0.53    k1_xboole_0 = sK0 | (~spl1_4 | ~spl1_8)),
% 1.33/0.53    inference(subsumption_resolution,[],[f193,f79])).
% 1.33/0.53  fof(f79,plain,(
% 1.33/0.53    v1_relat_1(sK0) | ~spl1_4),
% 1.33/0.53    inference(avatar_component_clause,[],[f77])).
% 1.33/0.53  fof(f193,plain,(
% 1.33/0.53    k1_xboole_0 = sK0 | ~v1_relat_1(sK0) | ~spl1_8),
% 1.33/0.53    inference(trivial_inequality_removal,[],[f192])).
% 1.33/0.53  % (4482)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.33/0.53  fof(f192,plain,(
% 1.33/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | ~v1_relat_1(sK0) | ~spl1_8),
% 1.33/0.53    inference(superposition,[],[f45,f182])).
% 1.33/0.53  fof(f45,plain,(
% 1.33/0.53    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f21])).
% 1.33/0.53  fof(f21,plain,(
% 1.33/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.33/0.53    inference(flattening,[],[f20])).
% 1.33/0.53  fof(f20,plain,(
% 1.33/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f7])).
% 1.33/0.53  fof(f7,axiom,(
% 1.33/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.33/0.53  fof(f190,plain,(
% 1.33/0.53    spl1_3 | ~spl1_4),
% 1.33/0.53    inference(avatar_contradiction_clause,[],[f189])).
% 1.33/0.53  fof(f189,plain,(
% 1.33/0.53    $false | (spl1_3 | ~spl1_4)),
% 1.33/0.53    inference(subsumption_resolution,[],[f188,f79])).
% 1.33/0.53  fof(f188,plain,(
% 1.33/0.53    ~v1_relat_1(sK0) | spl1_3),
% 1.33/0.53    inference(subsumption_resolution,[],[f187,f60])).
% 1.33/0.53  % (4475)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.53  fof(f60,plain,(
% 1.33/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.33/0.53    inference(equality_resolution,[],[f49])).
% 1.33/0.53  fof(f49,plain,(
% 1.33/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.33/0.53    inference(cnf_transformation,[],[f28])).
% 1.33/0.53  fof(f28,plain,(
% 1.33/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.53    inference(flattening,[],[f27])).
% 1.33/0.53  fof(f27,plain,(
% 1.33/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.33/0.53    inference(nnf_transformation,[],[f1])).
% 1.33/0.53  fof(f1,axiom,(
% 1.33/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.33/0.53  fof(f187,plain,(
% 1.33/0.53    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_3),
% 1.33/0.53    inference(subsumption_resolution,[],[f185,f60])).
% 1.33/0.53  fof(f185,plain,(
% 1.33/0.53    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_3),
% 1.33/0.53    inference(resolution,[],[f73,f39])).
% 1.33/0.53  fof(f39,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f19,plain,(
% 1.33/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.33/0.53    inference(flattening,[],[f18])).
% 1.33/0.53  fof(f18,plain,(
% 1.33/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.33/0.53    inference(ennf_transformation,[],[f9])).
% 1.33/0.53  fof(f9,axiom,(
% 1.33/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.33/0.53  fof(f73,plain,(
% 1.33/0.53    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl1_3),
% 1.33/0.53    inference(avatar_component_clause,[],[f71])).
% 1.33/0.53  fof(f71,plain,(
% 1.33/0.53    spl1_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.33/0.53  fof(f183,plain,(
% 1.33/0.53    spl1_8 | spl1_2 | ~spl1_4),
% 1.33/0.53    inference(avatar_split_clause,[],[f178,f77,f67,f180])).
% 1.33/0.53  fof(f178,plain,(
% 1.33/0.53    k1_xboole_0 = k2_relat_1(sK0) | (spl1_2 | ~spl1_4)),
% 1.33/0.53    inference(subsumption_resolution,[],[f177,f79])).
% 1.33/0.53  fof(f177,plain,(
% 1.33/0.53    k1_xboole_0 = k2_relat_1(sK0) | ~v1_relat_1(sK0) | spl1_2),
% 1.33/0.53    inference(subsumption_resolution,[],[f174,f60])).
% 1.33/0.53  fof(f174,plain,(
% 1.33/0.53    k1_xboole_0 = k2_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK0)) | ~v1_relat_1(sK0) | spl1_2),
% 1.33/0.53    inference(resolution,[],[f146,f69])).
% 1.33/0.53  fof(f146,plain,(
% 1.33/0.53    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | k1_xboole_0 = X0 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f143,f60])).
% 1.33/0.53  fof(f143,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~r1_tarski(k1_relat_1(X1),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.33/0.53    inference(resolution,[],[f142,f39])).
% 1.33/0.53  fof(f142,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | k1_xboole_0 = X1 | v1_funct_2(X0,k1_relat_1(X0),X1)) )),
% 1.33/0.53    inference(equality_resolution,[],[f136])).
% 1.33/0.53  fof(f136,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.53    inference(duplicate_literal_removal,[],[f134])).
% 1.33/0.53  fof(f134,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.53    inference(superposition,[],[f34,f38])).
% 1.33/0.53  fof(f34,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f24])).
% 1.33/0.53  fof(f97,plain,(
% 1.33/0.53    spl1_7),
% 1.33/0.53    inference(avatar_split_clause,[],[f92,f94])).
% 1.33/0.53  fof(f92,plain,(
% 1.33/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.33/0.53    inference(superposition,[],[f91,f52])).
% 1.33/0.53  fof(f52,plain,(
% 1.33/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f2])).
% 1.33/0.53  fof(f2,axiom,(
% 1.33/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.33/0.53  fof(f91,plain,(
% 1.33/0.53    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.33/0.53    inference(backward_demodulation,[],[f40,f51])).
% 1.33/0.53  fof(f51,plain,(
% 1.33/0.53    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f5])).
% 1.33/0.53  fof(f5,axiom,(
% 1.33/0.53    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.33/0.53  fof(f40,plain,(
% 1.33/0.53    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f4])).
% 1.33/0.53  fof(f4,axiom,(
% 1.33/0.53    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.33/0.53  fof(f90,plain,(
% 1.33/0.53    spl1_6),
% 1.33/0.53    inference(avatar_split_clause,[],[f46,f87])).
% 1.33/0.53  fof(f46,plain,(
% 1.33/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.53    inference(cnf_transformation,[],[f6])).
% 1.33/0.53  fof(f6,axiom,(
% 1.33/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.33/0.53  fof(f80,plain,(
% 1.33/0.53    spl1_4),
% 1.33/0.53    inference(avatar_split_clause,[],[f29,f77])).
% 1.33/0.53  fof(f29,plain,(
% 1.33/0.53    v1_relat_1(sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f23])).
% 1.33/0.53  fof(f23,plain,(
% 1.33/0.53    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.33/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f22])).
% 1.33/0.53  fof(f22,plain,(
% 1.33/0.53    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.33/0.53    introduced(choice_axiom,[])).
% 1.33/0.53  fof(f14,plain,(
% 1.33/0.53    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.33/0.53    inference(flattening,[],[f13])).
% 1.33/0.53  fof(f13,plain,(
% 1.33/0.53    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f12])).
% 1.33/0.53  fof(f12,negated_conjecture,(
% 1.33/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.33/0.53    inference(negated_conjecture,[],[f11])).
% 1.33/0.53  fof(f11,conjecture,(
% 1.33/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.33/0.53  fof(f75,plain,(
% 1.33/0.53    spl1_1),
% 1.33/0.53    inference(avatar_split_clause,[],[f30,f63])).
% 1.33/0.53  fof(f63,plain,(
% 1.33/0.53    spl1_1 <=> v1_funct_1(sK0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.33/0.53  fof(f30,plain,(
% 1.33/0.53    v1_funct_1(sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f23])).
% 1.33/0.53  fof(f74,plain,(
% 1.33/0.53    ~spl1_1 | ~spl1_2 | ~spl1_3),
% 1.33/0.53    inference(avatar_split_clause,[],[f31,f71,f67,f63])).
% 1.33/0.53  fof(f31,plain,(
% 1.33/0.53    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f23])).
% 1.33/0.53  % SZS output end Proof for theBenchmark
% 1.33/0.53  % (4496)------------------------------
% 1.33/0.53  % (4496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (4496)Termination reason: Refutation
% 1.33/0.53  
% 1.33/0.53  % (4496)Memory used [KB]: 6268
% 1.33/0.53  % (4496)Time elapsed: 0.118 s
% 1.33/0.53  % (4496)------------------------------
% 1.33/0.53  % (4496)------------------------------
% 1.33/0.54  % (4474)Success in time 0.178 s
%------------------------------------------------------------------------------
