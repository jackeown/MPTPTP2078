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
% DateTime   : Thu Dec  3 13:07:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 261 expanded)
%              Number of leaves         :   31 (  98 expanded)
%              Depth                    :    9
%              Number of atoms          :  422 ( 808 expanded)
%              Number of equality atoms :   34 (  51 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f64,f83,f88,f100,f105,f115,f130,f136,f146,f153,f178,f187,f199,f210,f232,f243,f251,f278,f305,f310,f314])).

fof(f314,plain,
    ( ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f311,f114])).

fof(f114,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_11
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f311,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

fof(f310,plain,
    ( ~ spl5_9
    | spl5_11
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl5_9
    | spl5_11
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f306,f135])).

fof(f135,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_14
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f306,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl5_9
    | spl5_11 ),
    inference(subsumption_resolution,[],[f254,f104])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f254,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f113,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f305,plain,
    ( ~ spl5_8
    | ~ spl5_20
    | spl5_25 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_20
    | spl5_25 ),
    inference(subsumption_resolution,[],[f301,f209])).

fof(f209,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_20
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f301,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_8
    | spl5_25 ),
    inference(resolution,[],[f286,f99])).

fof(f99,plain,
    ( r1_tarski(sK3,sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_8
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3,X0)
        | ~ r1_tarski(X0,k1_relat_1(sK2)) )
    | spl5_25 ),
    inference(superposition,[],[f279,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f279,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK3,X0),k1_relat_1(sK2))
    | spl5_25 ),
    inference(resolution,[],[f277,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f277,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl5_25
  <=> r1_tarski(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f278,plain,
    ( ~ spl5_25
    | ~ spl5_1
    | ~ spl5_13
    | spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f268,f143,f133,f127,f56,f275])).

fof(f56,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f127,plain,
    ( spl5_13
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f143,plain,
    ( spl5_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f268,plain,
    ( ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_13
    | spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f245,f128])).

fof(f128,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f245,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK3,k1_relat_1(sK2))
    | ~ spl5_1
    | spl5_14
    | ~ spl5_16 ),
    inference(resolution,[],[f134,f154])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_relat_1(sK2,X1))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X0,k1_relat_1(sK2)) )
    | ~ spl5_1
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f70,f144])).

fof(f144,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f58,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f58,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f134,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f251,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f249,f104])).

fof(f249,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_10
    | spl5_13 ),
    inference(subsumption_resolution,[],[f248,f129])).

fof(f129,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f248,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f243,plain,
    ( ~ spl5_14
    | ~ spl5_16
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_16
    | spl5_23 ),
    inference(subsumption_resolution,[],[f241,f144])).

fof(f241,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_14
    | spl5_23 ),
    inference(subsumption_resolution,[],[f239,f135])).

fof(f239,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ v1_relat_1(sK2)
    | spl5_23 ),
    inference(resolution,[],[f231,f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f231,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl5_23
  <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f232,plain,
    ( ~ spl5_23
    | spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f156,f140,f127,f229])).

fof(f140,plain,
    ( spl5_15
  <=> ! [X5] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f156,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))
    | spl5_13
    | ~ spl5_15 ),
    inference(resolution,[],[f138,f141])).

fof(f141,plain,
    ( ! [X5] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK4)
        | ~ r1_tarski(k9_relat_1(sK2,sK3),X0) )
    | spl5_13 ),
    inference(superposition,[],[f131,f42])).

fof(f131,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k9_relat_1(sK2,sK3),X0),sK4)
    | spl5_13 ),
    inference(resolution,[],[f129,f47])).

fof(f210,plain,
    ( spl5_20
    | ~ spl5_16
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f203,f184,f143,f207])).

fof(f184,plain,
    ( spl5_19
  <=> sK0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f203,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl5_16
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f202,f144])).

fof(f202,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl5_19 ),
    inference(superposition,[],[f41,f186])).

fof(f186,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f184])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f199,plain,
    ( spl5_2
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl5_2
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f188,f40])).

fof(f40,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f188,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_18 ),
    inference(superposition,[],[f63,f177])).

fof(f177,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl5_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f63,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f187,plain,
    ( spl5_19
    | ~ spl5_9
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f181,f171,f102,f184])).

fof(f171,plain,
    ( spl5_17
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f181,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ spl5_9
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f179,f104])).

fof(f179,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_17 ),
    inference(superposition,[],[f173,f53])).

fof(f173,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f171])).

fof(f178,plain,
    ( spl5_17
    | spl5_18
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f161,f102,f85,f56,f175,f171])).

fof(f85,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f161,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k8_relset_1(sK0,sK1,sK2,sK1)
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f160,f104])).

fof(f160,plain,
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
    inference(resolution,[],[f58,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f153,plain,
    ( ~ spl5_9
    | spl5_16 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl5_9
    | spl5_16 ),
    inference(resolution,[],[f147,f104])).

fof(f147,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_16 ),
    inference(resolution,[],[f145,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f145,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f143])).

% (1999)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (2006)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (1995)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (2005)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f146,plain,
    ( spl5_15
    | ~ spl5_16
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f73,f56,f143,f140])).

fof(f73,plain,
    ( ! [X5] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5) )
    | ~ spl5_1 ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

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
    inference(resolution,[],[f82,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:09:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (2000)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (1998)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (1998)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f315,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f59,f64,f83,f88,f100,f105,f115,f130,f136,f146,f153,f178,f187,f199,f210,f232,f243,f251,f278,f305,f310,f314])).
% 0.20/0.51  fof(f314,plain,(
% 0.20/0.51    ~spl5_10 | ~spl5_11),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f313])).
% 0.20/0.51  fof(f313,plain,(
% 0.20/0.51    $false | (~spl5_10 | ~spl5_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f311,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl5_11 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.51  fof(f311,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl5_10),
% 0.20/0.51    inference(subsumption_resolution,[],[f32,f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl5_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl5_10 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).
% 0.20/0.51  fof(f310,plain,(
% 0.20/0.51    ~spl5_9 | spl5_11 | ~spl5_14),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f309])).
% 0.20/0.51  fof(f309,plain,(
% 0.20/0.51    $false | (~spl5_9 | spl5_11 | ~spl5_14)),
% 0.20/0.51    inference(subsumption_resolution,[],[f306,f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl5_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f133])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl5_14 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.51  fof(f306,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | spl5_11)),
% 0.20/0.51    inference(subsumption_resolution,[],[f254,f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl5_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.51  fof(f254,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_11),
% 0.20/0.51    inference(superposition,[],[f113,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl5_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f112])).
% 0.20/0.51  fof(f305,plain,(
% 0.20/0.51    ~spl5_8 | ~spl5_20 | spl5_25),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f304])).
% 0.20/0.51  fof(f304,plain,(
% 0.20/0.51    $false | (~spl5_8 | ~spl5_20 | spl5_25)),
% 0.20/0.51    inference(subsumption_resolution,[],[f301,f209])).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl5_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f207])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    spl5_20 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.51  fof(f301,plain,(
% 0.20/0.51    ~r1_tarski(sK0,k1_relat_1(sK2)) | (~spl5_8 | spl5_25)),
% 0.20/0.51    inference(resolution,[],[f286,f99])).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    r1_tarski(sK3,sK0) | ~spl5_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f97])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    spl5_8 <=> r1_tarski(sK3,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.51  fof(f286,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(sK3,X0) | ~r1_tarski(X0,k1_relat_1(sK2))) ) | spl5_25),
% 0.20/0.51    inference(superposition,[],[f279,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.51  fof(f279,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK3,X0),k1_relat_1(sK2))) ) | spl5_25),
% 0.20/0.51    inference(resolution,[],[f277,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k1_relat_1(sK2)) | spl5_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f275])).
% 0.20/0.51  fof(f275,plain,(
% 0.20/0.51    spl5_25 <=> r1_tarski(sK3,k1_relat_1(sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.51  fof(f278,plain,(
% 0.20/0.51    ~spl5_25 | ~spl5_1 | ~spl5_13 | spl5_14 | ~spl5_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f268,f143,f133,f127,f56,f275])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    spl5_1 <=> v1_funct_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    spl5_13 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    spl5_16 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.51  fof(f268,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl5_1 | ~spl5_13 | spl5_14 | ~spl5_16)),
% 0.20/0.51    inference(subsumption_resolution,[],[f245,f128])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl5_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f127])).
% 0.20/0.51  fof(f245,plain,(
% 0.20/0.51    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~r1_tarski(sK3,k1_relat_1(sK2)) | (~spl5_1 | spl5_14 | ~spl5_16)),
% 0.20/0.51    inference(resolution,[],[f134,f154])).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(sK2,X1)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | ~r1_tarski(X0,k1_relat_1(sK2))) ) | (~spl5_1 | ~spl5_16)),
% 0.20/0.51    inference(subsumption_resolution,[],[f70,f144])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl5_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f143])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | ~spl5_1),
% 0.20/0.51    inference(resolution,[],[f58,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    v1_funct_1(sK2) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f56])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl5_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f133])).
% 0.20/0.51  fof(f251,plain,(
% 0.20/0.51    ~spl5_9 | ~spl5_10 | spl5_13),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f250])).
% 0.20/0.51  fof(f250,plain,(
% 0.20/0.51    $false | (~spl5_9 | ~spl5_10 | spl5_13)),
% 0.20/0.51    inference(subsumption_resolution,[],[f249,f104])).
% 0.20/0.51  fof(f249,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_10 | spl5_13)),
% 0.20/0.51    inference(subsumption_resolution,[],[f248,f129])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl5_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f127])).
% 0.20/0.51  fof(f248,plain,(
% 0.20/0.51    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_10),
% 0.20/0.51    inference(superposition,[],[f110,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.51  fof(f243,plain,(
% 0.20/0.51    ~spl5_14 | ~spl5_16 | spl5_23),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f242])).
% 0.20/0.51  fof(f242,plain,(
% 0.20/0.51    $false | (~spl5_14 | ~spl5_16 | spl5_23)),
% 0.20/0.51    inference(subsumption_resolution,[],[f241,f144])).
% 0.20/0.51  fof(f241,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | (~spl5_14 | spl5_23)),
% 0.20/0.51    inference(subsumption_resolution,[],[f239,f135])).
% 0.20/0.51  fof(f239,plain,(
% 0.20/0.51    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~v1_relat_1(sK2) | spl5_23),
% 0.20/0.51    inference(resolution,[],[f231,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    ~r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | spl5_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f229])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    spl5_23 <=> r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    ~spl5_23 | spl5_13 | ~spl5_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f156,f140,f127,f229])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    spl5_15 <=> ! [X5] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    ~r1_tarski(k9_relat_1(sK2,sK3),k9_relat_1(sK2,k10_relat_1(sK2,sK4))) | (spl5_13 | ~spl5_15)),
% 0.20/0.51    inference(resolution,[],[f138,f141])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    ( ! [X5] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5)) ) | ~spl5_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f140])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,sK4) | ~r1_tarski(k9_relat_1(sK2,sK3),X0)) ) | spl5_13),
% 0.20/0.51    inference(superposition,[],[f131,f42])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k2_xboole_0(k9_relat_1(sK2,sK3),X0),sK4)) ) | spl5_13),
% 0.20/0.51    inference(resolution,[],[f129,f47])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    spl5_20 | ~spl5_16 | ~spl5_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f203,f184,f143,f207])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    spl5_19 <=> sK0 = k10_relat_1(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.51  fof(f203,plain,(
% 0.20/0.51    r1_tarski(sK0,k1_relat_1(sK2)) | (~spl5_16 | ~spl5_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f202,f144])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl5_19),
% 0.20/0.51    inference(superposition,[],[f41,f186])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    sK0 = k10_relat_1(sK2,sK1) | ~spl5_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f184])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    spl5_2 | ~spl5_18),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f198])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    $false | (spl5_2 | ~spl5_18)),
% 0.20/0.51    inference(subsumption_resolution,[],[f188,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.51  fof(f188,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_18)),
% 0.20/0.51    inference(superposition,[],[f63,f177])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | ~spl5_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f175])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    spl5_18 <=> k1_xboole_0 = sK1),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ~v1_xboole_0(sK1) | spl5_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl5_2 <=> v1_xboole_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.51  fof(f187,plain,(
% 0.20/0.51    spl5_19 | ~spl5_9 | ~spl5_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f181,f171,f102,f184])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    spl5_17 <=> sK0 = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    sK0 = k10_relat_1(sK2,sK1) | (~spl5_9 | ~spl5_17)),
% 0.20/0.51    inference(subsumption_resolution,[],[f179,f104])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    sK0 = k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_17),
% 0.20/0.51    inference(superposition,[],[f173,f53])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | ~spl5_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f171])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    spl5_17 | spl5_18 | ~spl5_1 | ~spl5_6 | ~spl5_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f161,f102,f85,f56,f175,f171])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl5_1 | ~spl5_6 | ~spl5_9)),
% 0.20/0.51    inference(subsumption_resolution,[],[f160,f104])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k8_relset_1(sK0,sK1,sK2,sK1) | (~spl5_1 | ~spl5_6)),
% 0.20/0.51    inference(resolution,[],[f71,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl5_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f85])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X2,X3] : (~v1_funct_2(sK2,X2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = X3 | k8_relset_1(X2,X3,sK2,X3) = X2) ) | ~spl5_1),
% 0.20/0.51    inference(resolution,[],[f58,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    ~spl5_9 | spl5_16),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    $false | (~spl5_9 | spl5_16)),
% 0.20/0.51    inference(resolution,[],[f147,f104])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_16),
% 0.20/0.51    inference(resolution,[],[f145,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ~v1_relat_1(sK2) | spl5_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f143])).
% 0.20/0.51  % (1999)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (2006)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (1995)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (2005)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    spl5_15 | ~spl5_16 | ~spl5_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f73,f56,f143,f140])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X5] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X5)),X5)) ) | ~spl5_1),
% 0.20/0.52    inference(resolution,[],[f58,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    spl5_14 | ~spl5_9 | ~spl5_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f125,f112,f102,f133])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl5_9 | ~spl5_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f124,f104])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_11),
% 0.20/0.52    inference(superposition,[],[f114,f53])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    ~spl5_13 | ~spl5_9 | spl5_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f123,f108,f102,f127])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl5_9 | spl5_10)),
% 0.20/0.52    inference(subsumption_resolution,[],[f122,f104])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_10),
% 0.20/0.52    inference(superposition,[],[f109,f52])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl5_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f108])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    spl5_10 | spl5_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f31,f112,f108])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    spl5_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f102])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    spl5_8 | ~spl5_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f95,f80,f97])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    r1_tarski(sK3,sK0) | ~spl5_5),
% 0.20/0.52    inference(resolution,[],[f82,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f80])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl5_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f36,f85])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl5_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f34,f80])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ~spl5_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f38,f61])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ~v1_xboole_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl5_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f35,f56])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    v1_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (1998)------------------------------
% 0.20/0.52  % (1998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1998)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (1998)Memory used [KB]: 10746
% 0.20/0.52  % (1998)Time elapsed: 0.088 s
% 0.20/0.52  % (1998)------------------------------
% 0.20/0.52  % (1998)------------------------------
% 0.20/0.52  % (1994)Success in time 0.162 s
%------------------------------------------------------------------------------
