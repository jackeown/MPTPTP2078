%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:16 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 258 expanded)
%              Number of leaves         :   31 (  97 expanded)
%              Depth                    :    9
%              Number of atoms          :  427 ( 813 expanded)
%              Number of equality atoms :   31 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f83,f88,f100,f105,f115,f130,f136,f145,f151,f159,f164,f170,f187,f204,f217,f236,f247,f257,f262,f266])).

fof(f266,plain,
    ( ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f263,f114])).

fof(f114,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_11
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f263,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f32,f110])).

fof(f110,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_10
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f32,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) )
                      & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                  & m1_subset_1(X3,k1_zfmisc_1(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(X1))
                       => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                        <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(X1))
                     => ( r1_tarski(k7_relset_1(X0,X1,X2,X3),X4)
                      <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

fof(f262,plain,
    ( ~ spl5_9
    | spl5_11
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl5_9
    | spl5_11
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f174,f135])).

fof(f135,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_14
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f174,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9
    | spl5_11 ),
    inference(subsumption_resolution,[],[f173,f104])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f173,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_11 ),
    inference(superposition,[],[f113,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f113,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f257,plain,
    ( ~ spl5_16
    | spl5_20
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl5_16
    | spl5_20
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f255,f143])).

fof(f143,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f255,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_20
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f254,f203])).

fof(f203,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl5_20
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f254,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_24 ),
    inference(superposition,[],[f43,f235])).

fof(f235,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl5_24
  <=> sK0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f247,plain,
    ( spl5_2
    | ~ spl5_22 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl5_2
    | ~ spl5_22 ),
    inference(subsumption_resolution,[],[f237,f40])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f237,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_22 ),
    inference(superposition,[],[f63,f216])).

fof(f216,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl5_22
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f63,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f236,plain,
    ( spl5_24
    | ~ spl5_9
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f220,f210,f102,f233])).

fof(f210,plain,
    ( spl5_21
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f220,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl5_9
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f218,f104])).

fof(f218,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_21 ),
    inference(superposition,[],[f212,f53])).

fof(f212,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f210])).

fof(f217,plain,
    ( spl5_21
    | spl5_22
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f182,f102,f85,f56,f214,f210])).

fof(f56,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f85,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f182,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f181,f104])).

fof(f181,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(resolution,[],[f71,f87])).

fof(f87,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f71,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK2,X2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k1_xboole_0 = X3
        | k8_relset_1(X2,X3,sK2,X3) = X2 )
    | ~ spl5_1 ),
    inference(resolution,[],[f58,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f58,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f204,plain,
    ( ~ spl5_20
    | ~ spl5_8
    | spl5_18 ),
    inference(avatar_split_clause,[],[f189,f184,f97,f201])).

fof(f97,plain,
    ( spl5_8
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f184,plain,
    ( spl5_18
  <=> r1_tarski(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f189,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_8
    | spl5_18 ),
    inference(resolution,[],[f188,f99])).

fof(f99,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | ~ r1_tarski(X0,k1_relat_1(sK2)) )
    | spl5_18 ),
    inference(resolution,[],[f186,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f186,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f187,plain,
    ( ~ spl5_18
    | ~ spl5_1
    | ~ spl5_13
    | spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f177,f142,f133,f127,f56,f184])).

fof(f127,plain,
    ( spl5_13
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f177,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_13
    | spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f175,f128])).

fof(f128,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f175,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl5_1
    | spl5_14
    | ~ spl5_16 ),
    inference(resolution,[],[f134,f154])).

% (2491)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f154,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_relat_1(sK2,X1))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X0,k1_relat_1(sK2)) )
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f70,f143])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f134,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f170,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f168,f104])).

fof(f168,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f167,f129])).

fof(f129,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f167,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_10 ),
    inference(superposition,[],[f110,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f164,plain,
    ( ~ spl5_14
    | ~ spl5_16
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_16
    | spl5_17 ),
    inference(subsumption_resolution,[],[f162,f143])).

fof(f162,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_14
    | spl5_17 ),
    inference(subsumption_resolution,[],[f160,f135])).

fof(f160,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ v1_relat_1(sK2)
    | spl5_17 ),
    inference(resolution,[],[f158,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f158,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl5_17
  <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f159,plain,
    ( ~ spl5_17
    | spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f153,f139,f127,f156])).

fof(f139,plain,
    ( spl5_15
  <=> ! [X5] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f153,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | spl5_13
    | ~ spl5_15 ),
    inference(resolution,[],[f140,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(k9_relat_1(sK2,sK3),X0) )
    | spl5_13 ),
    inference(resolution,[],[f129,f51])).

fof(f140,plain,
    ( ! [X5] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f151,plain,
    ( ~ spl5_9
    | spl5_16 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl5_9
    | spl5_16 ),
    inference(subsumption_resolution,[],[f148,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f148,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_9
    | spl5_16 ),
    inference(resolution,[],[f146,f104])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_16 ),
    inference(resolution,[],[f144,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f144,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f142])).

fof(f145,plain,
    ( spl5_15
    | ~ spl5_16
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f73,f56,f142,f139])).

fof(f73,plain,
    ( ! [X5] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5) )
    | ~ spl5_1 ),
    inference(resolution,[],[f58,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f136,plain,
    ( spl5_14
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f125,f112,f102,f133])).

fof(f125,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f124,f104])).

fof(f124,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_11 ),
    inference(superposition,[],[f114,f53])).

fof(f130,plain,
    ( ~ spl5_13
    | ~ spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f123,f108,f102,f127])).

fof(f123,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_9
    | spl5_10 ),
    inference(subsumption_resolution,[],[f122,f104])).

fof(f122,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_10 ),
    inference(superposition,[],[f109,f52])).

fof(f109,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f115,plain,
    ( spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f31,f112,f108])).

fof(f31,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f37,f102])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f100,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f95,f80,f97])).

fof(f80,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f95,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f82,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f82,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f88,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f36,f85])).

fof(f36,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f38,f61])).

fof(f38,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f35,f56])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:22:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.42  % (2497)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.45  % (2498)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.45  % (2494)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.18/0.45  % (2487)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.46  % (2490)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.46  % (2502)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.18/0.46  % (2487)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.47  % (2485)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.47  % (2484)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.47  % SZS output start Proof for theBenchmark
% 0.18/0.47  fof(f267,plain,(
% 0.18/0.47    $false),
% 0.18/0.47    inference(avatar_sat_refutation,[],[f59,f64,f83,f88,f100,f105,f115,f130,f136,f145,f151,f159,f164,f170,f187,f204,f217,f236,f247,f257,f262,f266])).
% 0.18/0.47  fof(f266,plain,(
% 0.18/0.47    ~spl5_10 | ~spl5_11),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f265])).
% 0.18/0.47  fof(f265,plain,(
% 0.18/0.47    $false | (~spl5_10 | ~spl5_11)),
% 0.18/0.47    inference(subsumption_resolution,[],[f263,f114])).
% 0.18/0.47  fof(f114,plain,(
% 0.18/0.47    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_11),
% 0.18/0.47    inference(avatar_component_clause,[],[f112])).
% 0.18/0.47  fof(f112,plain,(
% 0.18/0.47    spl5_11 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.18/0.47  fof(f263,plain,(
% 0.18/0.47    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_10),
% 0.18/0.47    inference(subsumption_resolution,[],[f32,f110])).
% 0.18/0.47  fof(f110,plain,(
% 0.18/0.47    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl5_10),
% 0.18/0.47    inference(avatar_component_clause,[],[f108])).
% 0.18/0.47  fof(f108,plain,(
% 0.18/0.47    spl5_10 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.18/0.47  fof(f32,plain,(
% 0.18/0.47    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.18/0.47    inference(flattening,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f14])).
% 0.18/0.47  fof(f14,negated_conjecture,(
% 0.18/0.47    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.18/0.47    inference(negated_conjecture,[],[f13])).
% 0.18/0.47  fof(f13,conjecture,(
% 0.18/0.47    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).
% 0.18/0.47  fof(f262,plain,(
% 0.18/0.47    ~spl5_9 | spl5_11 | ~spl5_14),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f261])).
% 0.18/0.47  fof(f261,plain,(
% 0.18/0.47    $false | (~spl5_9 | spl5_11 | ~spl5_14)),
% 0.18/0.47    inference(subsumption_resolution,[],[f174,f135])).
% 0.18/0.47  fof(f135,plain,(
% 0.18/0.47    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl5_14),
% 0.18/0.47    inference(avatar_component_clause,[],[f133])).
% 0.18/0.47  fof(f133,plain,(
% 0.18/0.47    spl5_14 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.18/0.47  fof(f174,plain,(
% 0.18/0.47    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | spl5_11)),
% 0.18/0.47    inference(subsumption_resolution,[],[f173,f104])).
% 0.18/0.47  fof(f104,plain,(
% 0.18/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_9),
% 0.18/0.47    inference(avatar_component_clause,[],[f102])).
% 0.18/0.47  fof(f102,plain,(
% 0.18/0.47    spl5_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.18/0.47  fof(f173,plain,(
% 0.18/0.47    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_11),
% 0.18/0.47    inference(superposition,[],[f113,f53])).
% 0.18/0.47  fof(f53,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f30])).
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f11])).
% 0.18/0.47  fof(f11,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.18/0.47  fof(f113,plain,(
% 0.18/0.47    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl5_11),
% 0.18/0.47    inference(avatar_component_clause,[],[f112])).
% 0.18/0.47  fof(f257,plain,(
% 0.18/0.47    ~spl5_16 | spl5_20 | ~spl5_24),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f256])).
% 0.18/0.47  fof(f256,plain,(
% 0.18/0.47    $false | (~spl5_16 | spl5_20 | ~spl5_24)),
% 0.18/0.47    inference(subsumption_resolution,[],[f255,f143])).
% 0.18/0.47  fof(f143,plain,(
% 0.18/0.47    v1_relat_1(sK2) | ~spl5_16),
% 0.18/0.47    inference(avatar_component_clause,[],[f142])).
% 0.18/0.47  fof(f142,plain,(
% 0.18/0.47    spl5_16 <=> v1_relat_1(sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.18/0.47  fof(f255,plain,(
% 0.18/0.47    ~v1_relat_1(sK2) | (spl5_20 | ~spl5_24)),
% 0.18/0.47    inference(subsumption_resolution,[],[f254,f203])).
% 0.18/0.47  fof(f203,plain,(
% 0.18/0.47    ~r1_tarski(sK0,k1_relat_1(sK2)) | spl5_20),
% 0.18/0.47    inference(avatar_component_clause,[],[f201])).
% 0.18/0.47  fof(f201,plain,(
% 0.18/0.47    spl5_20 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.18/0.47  fof(f254,plain,(
% 0.18/0.47    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl5_24),
% 0.18/0.47    inference(superposition,[],[f43,f235])).
% 0.18/0.47  fof(f235,plain,(
% 0.18/0.47    sK0 = k10_relat_1(sK2,sK1) | ~spl5_24),
% 0.18/0.47    inference(avatar_component_clause,[],[f233])).
% 0.18/0.47  fof(f233,plain,(
% 0.18/0.47    spl5_24 <=> sK0 = k10_relat_1(sK2,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.18/0.47  fof(f43,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f7])).
% 0.18/0.47  fof(f7,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.18/0.47  fof(f247,plain,(
% 0.18/0.47    spl5_2 | ~spl5_22),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f246])).
% 0.18/0.47  fof(f246,plain,(
% 0.18/0.47    $false | (spl5_2 | ~spl5_22)),
% 0.18/0.47    inference(subsumption_resolution,[],[f237,f40])).
% 0.18/0.47  fof(f40,plain,(
% 0.18/0.47    v1_xboole_0(k1_xboole_0)),
% 0.18/0.47    inference(cnf_transformation,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    v1_xboole_0(k1_xboole_0)),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.18/0.47  fof(f237,plain,(
% 0.18/0.47    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_22)),
% 0.18/0.47    inference(superposition,[],[f63,f216])).
% 0.18/0.47  fof(f216,plain,(
% 0.18/0.47    k1_xboole_0 = sK1 | ~spl5_22),
% 0.18/0.47    inference(avatar_component_clause,[],[f214])).
% 0.18/0.47  fof(f214,plain,(
% 0.18/0.47    spl5_22 <=> k1_xboole_0 = sK1),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.18/0.47  fof(f63,plain,(
% 0.18/0.47    ~v1_xboole_0(sK1) | spl5_2),
% 0.18/0.47    inference(avatar_component_clause,[],[f61])).
% 0.18/0.47  fof(f61,plain,(
% 0.18/0.47    spl5_2 <=> v1_xboole_0(sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.18/0.47  fof(f236,plain,(
% 0.18/0.47    spl5_24 | ~spl5_9 | ~spl5_21),
% 0.18/0.47    inference(avatar_split_clause,[],[f220,f210,f102,f233])).
% 0.18/0.47  fof(f210,plain,(
% 0.18/0.47    spl5_21 <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.18/0.47  fof(f220,plain,(
% 0.18/0.47    sK0 = k10_relat_1(sK2,sK1) | (~spl5_9 | ~spl5_21)),
% 0.18/0.47    inference(subsumption_resolution,[],[f218,f104])).
% 0.18/0.47  fof(f218,plain,(
% 0.18/0.47    sK0 = k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_21),
% 0.18/0.47    inference(superposition,[],[f212,f53])).
% 0.18/0.47  fof(f212,plain,(
% 0.18/0.47    sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl5_21),
% 0.18/0.47    inference(avatar_component_clause,[],[f210])).
% 0.18/0.47  fof(f217,plain,(
% 0.18/0.47    spl5_21 | spl5_22 | ~spl5_1 | ~spl5_6 | ~spl5_9),
% 0.18/0.47    inference(avatar_split_clause,[],[f182,f102,f85,f56,f214,f210])).
% 0.18/0.47  fof(f56,plain,(
% 0.18/0.47    spl5_1 <=> v1_funct_1(sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.18/0.47  fof(f85,plain,(
% 0.18/0.47    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.18/0.47  fof(f182,plain,(
% 0.18/0.47    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl5_1 | ~spl5_6 | ~spl5_9)),
% 0.18/0.47    inference(subsumption_resolution,[],[f181,f104])).
% 0.18/0.47  fof(f181,plain,(
% 0.18/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl5_1 | ~spl5_6)),
% 0.18/0.47    inference(resolution,[],[f71,f87])).
% 0.18/0.47  fof(f87,plain,(
% 0.18/0.47    v1_funct_2(sK2,sK0,sK1) | ~spl5_6),
% 0.18/0.47    inference(avatar_component_clause,[],[f85])).
% 0.18/0.47  fof(f71,plain,(
% 0.18/0.47    ( ! [X2,X3] : (~v1_funct_2(sK2,X2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = X3 | k8_relset_1(X2,X3,sK2,X3) = X2) ) | ~spl5_1),
% 0.18/0.47    inference(resolution,[],[f58,f48])).
% 0.18/0.47  fof(f48,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.18/0.47    inference(cnf_transformation,[],[f24])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.18/0.47    inference(flattening,[],[f23])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.18/0.47    inference(ennf_transformation,[],[f12])).
% 0.18/0.47  fof(f12,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 0.18/0.47  fof(f58,plain,(
% 0.18/0.47    v1_funct_1(sK2) | ~spl5_1),
% 0.18/0.47    inference(avatar_component_clause,[],[f56])).
% 0.18/0.47  fof(f204,plain,(
% 0.18/0.47    ~spl5_20 | ~spl5_8 | spl5_18),
% 0.18/0.47    inference(avatar_split_clause,[],[f189,f184,f97,f201])).
% 0.18/0.47  fof(f97,plain,(
% 0.18/0.47    spl5_8 <=> r1_tarski(sK3,sK0)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.18/0.47  fof(f184,plain,(
% 0.18/0.47    spl5_18 <=> r1_tarski(sK3,k1_relat_1(sK2))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.18/0.47  fof(f189,plain,(
% 0.18/0.47    ~r1_tarski(sK0,k1_relat_1(sK2)) | (~spl5_8 | spl5_18)),
% 0.18/0.47    inference(resolution,[],[f188,f99])).
% 0.18/0.47  fof(f99,plain,(
% 0.18/0.47    r1_tarski(sK3,sK0) | ~spl5_8),
% 0.18/0.47    inference(avatar_component_clause,[],[f97])).
% 0.18/0.47  fof(f188,plain,(
% 0.18/0.47    ( ! [X0] : (~r1_tarski(sK3,X0) | ~r1_tarski(X0,k1_relat_1(sK2))) ) | spl5_18),
% 0.18/0.47    inference(resolution,[],[f186,f51])).
% 0.18/0.47  fof(f51,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f28])).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.18/0.47    inference(flattening,[],[f27])).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.18/0.47    inference(ennf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.18/0.47  fof(f186,plain,(
% 0.18/0.47    ~r1_tarski(sK3,k1_relat_1(sK2)) | spl5_18),
% 0.18/0.47    inference(avatar_component_clause,[],[f184])).
% 0.18/0.47  fof(f187,plain,(
% 0.18/0.47    ~spl5_18 | ~spl5_1 | ~spl5_13 | spl5_14 | ~spl5_16),
% 0.18/0.47    inference(avatar_split_clause,[],[f177,f142,f133,f127,f56,f184])).
% 0.18/0.47  fof(f127,plain,(
% 0.18/0.47    spl5_13 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.18/0.47  fof(f177,plain,(
% 0.18/0.47    ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl5_1 | ~spl5_13 | spl5_14 | ~spl5_16)),
% 0.18/0.47    inference(subsumption_resolution,[],[f175,f128])).
% 0.18/0.47  fof(f128,plain,(
% 0.18/0.47    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_13),
% 0.18/0.47    inference(avatar_component_clause,[],[f127])).
% 0.18/0.47  fof(f175,plain,(
% 0.18/0.47    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl5_1 | spl5_14 | ~spl5_16)),
% 0.18/0.47    inference(resolution,[],[f134,f154])).
% 0.18/0.47  % (2491)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.18/0.47  fof(f154,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(sK2,X1)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | ~r1_tarski(X0,k1_relat_1(sK2))) ) | (~spl5_1 | ~spl5_16)),
% 0.18/0.47    inference(subsumption_resolution,[],[f70,f143])).
% 0.18/0.47  fof(f70,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | ~spl5_1),
% 0.18/0.47    inference(resolution,[],[f58,f50])).
% 0.18/0.47  fof(f50,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f26])).
% 0.18/0.47  fof(f26,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.18/0.47    inference(flattening,[],[f25])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.18/0.47    inference(ennf_transformation,[],[f9])).
% 0.18/0.47  fof(f9,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 0.18/0.47  fof(f134,plain,(
% 0.18/0.47    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl5_14),
% 0.18/0.47    inference(avatar_component_clause,[],[f133])).
% 0.18/0.47  fof(f170,plain,(
% 0.18/0.47    ~spl5_9 | ~spl5_10 | spl5_13),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f169])).
% 0.18/0.47  fof(f169,plain,(
% 0.18/0.47    $false | (~spl5_9 | ~spl5_10 | spl5_13)),
% 0.18/0.47    inference(subsumption_resolution,[],[f168,f104])).
% 0.18/0.47  fof(f168,plain,(
% 0.18/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_10 | spl5_13)),
% 0.18/0.47    inference(subsumption_resolution,[],[f167,f129])).
% 0.18/0.47  fof(f129,plain,(
% 0.18/0.47    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl5_13),
% 0.18/0.47    inference(avatar_component_clause,[],[f127])).
% 0.18/0.47  fof(f167,plain,(
% 0.18/0.47    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_10),
% 0.18/0.47    inference(superposition,[],[f110,f52])).
% 0.18/0.47  fof(f52,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f29])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f10])).
% 0.18/0.47  fof(f10,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.18/0.47  fof(f164,plain,(
% 0.18/0.47    ~spl5_14 | ~spl5_16 | spl5_17),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f163])).
% 0.18/0.47  fof(f163,plain,(
% 0.18/0.47    $false | (~spl5_14 | ~spl5_16 | spl5_17)),
% 0.18/0.47    inference(subsumption_resolution,[],[f162,f143])).
% 0.18/0.47  fof(f162,plain,(
% 0.18/0.47    ~v1_relat_1(sK2) | (~spl5_14 | spl5_17)),
% 0.18/0.47    inference(subsumption_resolution,[],[f160,f135])).
% 0.18/0.47  fof(f160,plain,(
% 0.18/0.47    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~v1_relat_1(sK2) | spl5_17),
% 0.18/0.47    inference(resolution,[],[f158,f47])).
% 0.18/0.47  fof(f47,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f22])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.18/0.47    inference(flattening,[],[f21])).
% 0.18/0.47  fof(f21,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.18/0.47    inference(ennf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.18/0.47  fof(f158,plain,(
% 0.18/0.47    ~r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | spl5_17),
% 0.18/0.47    inference(avatar_component_clause,[],[f156])).
% 0.18/0.47  fof(f156,plain,(
% 0.18/0.47    spl5_17 <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.18/0.47  fof(f159,plain,(
% 0.18/0.47    ~spl5_17 | spl5_13 | ~spl5_15),
% 0.18/0.47    inference(avatar_split_clause,[],[f153,f139,f127,f156])).
% 0.18/0.47  fof(f139,plain,(
% 0.18/0.47    spl5_15 <=> ! [X5] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.18/0.47  fof(f153,plain,(
% 0.18/0.47    ~r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | (spl5_13 | ~spl5_15)),
% 0.18/0.47    inference(resolution,[],[f140,f131])).
% 0.18/0.47  fof(f131,plain,(
% 0.18/0.47    ( ! [X0] : (~r1_tarski(X0,sK4) | ~r1_tarski(k9_relat_1(sK2,sK3),X0)) ) | spl5_13),
% 0.18/0.47    inference(resolution,[],[f129,f51])).
% 0.18/0.47  fof(f140,plain,(
% 0.18/0.47    ( ! [X5] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5)) ) | ~spl5_15),
% 0.18/0.47    inference(avatar_component_clause,[],[f139])).
% 0.18/0.47  fof(f151,plain,(
% 0.18/0.47    ~spl5_9 | spl5_16),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f150])).
% 0.18/0.47  fof(f150,plain,(
% 0.18/0.47    $false | (~spl5_9 | spl5_16)),
% 0.18/0.47    inference(subsumption_resolution,[],[f148,f42])).
% 0.18/0.47  fof(f42,plain,(
% 0.18/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.18/0.47  fof(f148,plain,(
% 0.18/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl5_9 | spl5_16)),
% 0.18/0.47    inference(resolution,[],[f146,f104])).
% 0.18/0.47  fof(f146,plain,(
% 0.18/0.47    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_16),
% 0.18/0.47    inference(resolution,[],[f144,f41])).
% 0.18/0.47  fof(f41,plain,(
% 0.18/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f17])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.18/0.47  fof(f144,plain,(
% 0.18/0.47    ~v1_relat_1(sK2) | spl5_16),
% 0.18/0.47    inference(avatar_component_clause,[],[f142])).
% 0.18/0.47  fof(f145,plain,(
% 0.18/0.47    spl5_15 | ~spl5_16 | ~spl5_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f73,f56,f142,f139])).
% 0.18/0.47  fof(f73,plain,(
% 0.18/0.47    ( ! [X5] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5)) ) | ~spl5_1),
% 0.18/0.47    inference(resolution,[],[f58,f44])).
% 0.18/0.47  fof(f44,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(flattening,[],[f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.18/0.47    inference(ennf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,axiom,(
% 0.18/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.18/0.47  fof(f136,plain,(
% 0.18/0.47    spl5_14 | ~spl5_9 | ~spl5_11),
% 0.18/0.47    inference(avatar_split_clause,[],[f125,f112,f102,f133])).
% 0.18/0.47  fof(f125,plain,(
% 0.18/0.47    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | ~spl5_11)),
% 0.18/0.47    inference(subsumption_resolution,[],[f124,f104])).
% 0.18/0.47  fof(f124,plain,(
% 0.18/0.47    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_11),
% 0.18/0.47    inference(superposition,[],[f114,f53])).
% 0.18/0.47  fof(f130,plain,(
% 0.18/0.47    ~spl5_13 | ~spl5_9 | spl5_10),
% 0.18/0.47    inference(avatar_split_clause,[],[f123,f108,f102,f127])).
% 0.18/0.47  fof(f123,plain,(
% 0.18/0.47    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_9 | spl5_10)),
% 0.18/0.47    inference(subsumption_resolution,[],[f122,f104])).
% 0.18/0.47  fof(f122,plain,(
% 0.18/0.47    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_10),
% 0.18/0.47    inference(superposition,[],[f109,f52])).
% 0.18/0.47  fof(f109,plain,(
% 0.18/0.47    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl5_10),
% 0.18/0.47    inference(avatar_component_clause,[],[f108])).
% 0.18/0.47  fof(f115,plain,(
% 0.18/0.47    spl5_10 | spl5_11),
% 0.18/0.47    inference(avatar_split_clause,[],[f31,f112,f108])).
% 0.18/0.47  fof(f31,plain,(
% 0.18/0.47    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  fof(f105,plain,(
% 0.18/0.47    spl5_9),
% 0.18/0.47    inference(avatar_split_clause,[],[f37,f102])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  fof(f100,plain,(
% 0.18/0.47    spl5_8 | ~spl5_5),
% 0.18/0.47    inference(avatar_split_clause,[],[f95,f80,f97])).
% 0.18/0.47  fof(f80,plain,(
% 0.18/0.47    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.18/0.47  fof(f95,plain,(
% 0.18/0.47    r1_tarski(sK3,sK0) | ~spl5_5),
% 0.18/0.47    inference(resolution,[],[f82,f46])).
% 0.18/0.47  fof(f46,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f3])).
% 0.18/0.47  fof(f3,axiom,(
% 0.18/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.18/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.18/0.47  fof(f82,plain,(
% 0.18/0.47    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.18/0.47    inference(avatar_component_clause,[],[f80])).
% 0.18/0.47  fof(f88,plain,(
% 0.18/0.47    spl5_6),
% 0.18/0.47    inference(avatar_split_clause,[],[f36,f85])).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    v1_funct_2(sK2,sK0,sK1)),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  fof(f83,plain,(
% 0.18/0.47    spl5_5),
% 0.18/0.47    inference(avatar_split_clause,[],[f34,f80])).
% 0.18/0.47  fof(f34,plain,(
% 0.18/0.47    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  fof(f64,plain,(
% 0.18/0.47    ~spl5_2),
% 0.18/0.47    inference(avatar_split_clause,[],[f38,f61])).
% 0.18/0.47  fof(f38,plain,(
% 0.18/0.47    ~v1_xboole_0(sK1)),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  fof(f59,plain,(
% 0.18/0.47    spl5_1),
% 0.18/0.47    inference(avatar_split_clause,[],[f35,f56])).
% 0.18/0.47  fof(f35,plain,(
% 0.18/0.47    v1_funct_1(sK2)),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.47  % (2487)------------------------------
% 0.18/0.47  % (2487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (2487)Termination reason: Refutation
% 0.18/0.47  
% 0.18/0.47  % (2487)Memory used [KB]: 10746
% 0.18/0.47  % (2487)Time elapsed: 0.066 s
% 0.18/0.47  % (2487)------------------------------
% 0.18/0.47  % (2487)------------------------------
% 0.18/0.48  % (2483)Success in time 0.132 s
%------------------------------------------------------------------------------
