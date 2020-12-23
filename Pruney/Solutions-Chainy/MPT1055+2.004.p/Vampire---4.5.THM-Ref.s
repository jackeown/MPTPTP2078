%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 240 expanded)
%              Number of leaves         :   31 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  433 ( 781 expanded)
%              Number of equality atoms :   41 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f98,f103,f109,f119,f131,f138,f155,f165,f177,f186,f200,f218,f294,f300,f307,f336,f340,f347])).

fof(f347,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_8
    | spl6_10 ),
    inference(subsumption_resolution,[],[f341,f130])).

fof(f130,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_10
  <=> r1_tarski(k9_relat_1(sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f341,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f296,f108])).

fof(f108,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f296,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_8 ),
    inference(superposition,[],[f114,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f114,plain,
    ( r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_8
  <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f340,plain,
    ( ~ spl6_5
    | spl6_30 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | ~ spl6_5
    | spl6_30 ),
    inference(subsumption_resolution,[],[f338,f97])).

fof(f97,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f338,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl6_30 ),
    inference(resolution,[],[f335,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f335,plain,
    ( ~ r1_tarski(sK3,sK0)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl6_30
  <=> r1_tarski(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f336,plain,
    ( ~ spl6_30
    | ~ spl6_1
    | ~ spl6_10
    | spl6_11
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f312,f183,f152,f135,f128,f71,f333])).

fof(f71,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f135,plain,
    ( spl6_11
  <=> r1_tarski(sK3,k10_relat_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f152,plain,
    ( spl6_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f183,plain,
    ( spl6_18
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f312,plain,
    ( ~ r1_tarski(sK3,sK0)
    | ~ spl6_1
    | ~ spl6_10
    | spl6_11
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f309,f129])).

fof(f129,plain,
    ( r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f309,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ r1_tarski(sK3,sK0)
    | ~ spl6_1
    | spl6_11
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(resolution,[],[f136,f222])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k10_relat_1(sK2,X1))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | ~ r1_tarski(X0,sK0) )
    | ~ spl6_1
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f219,f153])).

fof(f153,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v1_relat_1(sK2)
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_1
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f85,f185])).

fof(f185,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | ~ r1_tarski(k9_relat_1(sK2,X0),X1)
        | r1_tarski(X0,k10_relat_1(sK2,X1)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | r1_tarski(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

fof(f73,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f136,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f307,plain,
    ( ~ spl6_7
    | spl6_9
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl6_7
    | spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f305,f108])).

fof(f305,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_9
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f304,f137])).

fof(f137,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f304,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_9 ),
    inference(superposition,[],[f117,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f117,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_9
  <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f300,plain,
    ( ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f295,f114])).

fof(f295,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f37,f118])).

fof(f118,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f37,plain,
    ( ~ r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f294,plain,
    ( spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f290,f137])).

fof(f290,plain,
    ( ~ r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | spl6_10
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(resolution,[],[f240,f150])).

fof(f150,plain,
    ( ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl6_13
  <=> ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),sK4)
        | ~ r1_tarski(sK3,X0) )
    | spl6_10
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f236,f153])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,X0),sK4)
        | ~ r1_tarski(sK3,X0)
        | ~ v1_relat_1(sK2) )
    | spl6_10 ),
    inference(resolution,[],[f132,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f132,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k9_relat_1(sK2,sK3),X0)
        | ~ r1_tarski(X0,sK4) )
    | spl6_10 ),
    inference(resolution,[],[f130,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f218,plain,
    ( ~ spl6_7
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl6_7
    | spl6_14 ),
    inference(resolution,[],[f156,f108])).

fof(f156,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_14 ),
    inference(resolution,[],[f154,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f154,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f200,plain,
    ( spl6_15
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f197,f45])).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f197,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5(k1_xboole_0))
    | spl6_15
    | ~ spl6_17 ),
    inference(superposition,[],[f164,f176])).

fof(f176,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl6_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f164,plain,
    ( ~ r1_tarski(sK1,sK5(sK1))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl6_15
  <=> r1_tarski(sK1,sK5(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f186,plain,
    ( spl6_18
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f180,f170,f106,f183])).

fof(f170,plain,
    ( spl6_16
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f180,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f178,f108])).

fof(f178,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(superposition,[],[f172,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f172,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f170])).

fof(f177,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f166,f106,f100,f174,f170])).

fof(f100,plain,
    ( spl6_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f166,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f104,f108])).

fof(f104,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f102,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f102,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f165,plain,
    ( ~ spl6_15
    | spl6_2 ),
    inference(avatar_split_clause,[],[f144,f76,f162])).

fof(f76,plain,
    ( spl6_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f144,plain,
    ( ~ r1_tarski(sK1,sK5(sK1))
    | spl6_2 ),
    inference(resolution,[],[f110,f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ r1_tarski(sK1,X0) )
    | spl6_2 ),
    inference(resolution,[],[f87,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f87,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK1) )
    | spl6_2 ),
    inference(resolution,[],[f78,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f78,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f155,plain,
    ( spl6_13
    | ~ spl6_14
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f86,f71,f152,f149])).

fof(f86,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f138,plain,
    ( spl6_11
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f126,f116,f106,f135])).

fof(f126,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f125,f108])).

fof(f125,plain,
    ( r1_tarski(sK3,k10_relat_1(sK2,sK4))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_9 ),
    inference(superposition,[],[f118,f63])).

fof(f131,plain,
    ( ~ spl6_10
    | ~ spl6_7
    | spl6_8 ),
    inference(avatar_split_clause,[],[f124,f112,f106,f128])).

fof(f124,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ spl6_7
    | spl6_8 ),
    inference(subsumption_resolution,[],[f123,f108])).

fof(f123,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,sK3),sK4)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_8 ),
    inference(superposition,[],[f113,f64])).

fof(f113,plain,
    ( ~ r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f119,plain,
    ( spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f36,f116,f112])).

fof(f36,plain,
    ( r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))
    | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f42,f106])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f41,f100])).

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f39,f95])).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f43,f76])).

fof(f43,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f40,f71])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:28:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (25296)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (25294)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (25288)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (25289)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (25286)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (25297)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (25281)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (25284)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (25284)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (25292)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.53  % (25285)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (25287)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.54  % (25283)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.54  % (25290)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.54  % (25282)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (25291)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.54  % (25295)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f348,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f74,f79,f98,f103,f109,f119,f131,f138,f155,f165,f177,f186,f200,f218,f294,f300,f307,f336,f340,f347])).
% 0.22/0.54  fof(f347,plain,(
% 0.22/0.54    ~spl6_7 | ~spl6_8 | spl6_10),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f346])).
% 0.22/0.54  fof(f346,plain,(
% 0.22/0.54    $false | (~spl6_7 | ~spl6_8 | spl6_10)),
% 0.22/0.54    inference(subsumption_resolution,[],[f341,f130])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | spl6_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f128])).
% 0.22/0.54  fof(f128,plain,(
% 0.22/0.54    spl6_10 <=> r1_tarski(k9_relat_1(sK2,sK3),sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.54  fof(f341,plain,(
% 0.22/0.54    r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl6_7 | ~spl6_8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f296,f108])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f106])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    spl6_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.54  fof(f296,plain,(
% 0.22/0.54    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_8),
% 0.22/0.54    inference(superposition,[],[f114,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl6_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    spl6_8 <=> r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.54  fof(f340,plain,(
% 0.22/0.54    ~spl6_5 | spl6_30),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f339])).
% 0.22/0.54  fof(f339,plain,(
% 0.22/0.54    $false | (~spl6_5 | spl6_30)),
% 0.22/0.54    inference(subsumption_resolution,[],[f338,f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.54  fof(f338,plain,(
% 0.22/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl6_30),
% 0.22/0.54    inference(resolution,[],[f335,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    ~r1_tarski(sK3,sK0) | spl6_30),
% 0.22/0.54    inference(avatar_component_clause,[],[f333])).
% 0.22/0.54  fof(f333,plain,(
% 0.22/0.54    spl6_30 <=> r1_tarski(sK3,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.54  fof(f336,plain,(
% 0.22/0.54    ~spl6_30 | ~spl6_1 | ~spl6_10 | spl6_11 | ~spl6_14 | ~spl6_18),
% 0.22/0.54    inference(avatar_split_clause,[],[f312,f183,f152,f135,f128,f71,f333])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    spl6_1 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    spl6_11 <=> r1_tarski(sK3,k10_relat_1(sK2,sK4))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.54  fof(f152,plain,(
% 0.22/0.54    spl6_14 <=> v1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    spl6_18 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.54  fof(f312,plain,(
% 0.22/0.54    ~r1_tarski(sK3,sK0) | (~spl6_1 | ~spl6_10 | spl6_11 | ~spl6_14 | ~spl6_18)),
% 0.22/0.54    inference(subsumption_resolution,[],[f309,f129])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~spl6_10),
% 0.22/0.54    inference(avatar_component_clause,[],[f128])).
% 0.22/0.54  fof(f309,plain,(
% 0.22/0.54    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~r1_tarski(sK3,sK0) | (~spl6_1 | spl6_11 | ~spl6_14 | ~spl6_18)),
% 0.22/0.54    inference(resolution,[],[f136,f222])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(sK2,X1)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | ~r1_tarski(X0,sK0)) ) | (~spl6_1 | ~spl6_14 | ~spl6_18)),
% 0.22/0.54    inference(subsumption_resolution,[],[f219,f153])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    v1_relat_1(sK2) | ~spl6_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f152])).
% 0.22/0.54  fof(f219,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,sK0) | ~v1_relat_1(sK2) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | (~spl6_1 | ~spl6_18)),
% 0.22/0.54    inference(forward_demodulation,[],[f85,f185])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK2) | ~spl6_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f183])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~r1_tarski(X0,k1_relat_1(sK2)) | ~r1_tarski(k9_relat_1(sK2,X0),X1) | r1_tarski(X0,k10_relat_1(sK2,X1))) ) | ~spl6_1),
% 0.22/0.54    inference(resolution,[],[f73,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(X0,k1_relat_1(X2)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | r1_tarski(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    v1_funct_1(sK2) | ~spl6_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f71])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | spl6_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f135])).
% 0.22/0.54  fof(f307,plain,(
% 0.22/0.54    ~spl6_7 | spl6_9 | ~spl6_11),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f306])).
% 0.22/0.54  fof(f306,plain,(
% 0.22/0.54    $false | (~spl6_7 | spl6_9 | ~spl6_11)),
% 0.22/0.54    inference(subsumption_resolution,[],[f305,f108])).
% 0.22/0.54  fof(f305,plain,(
% 0.22/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl6_9 | ~spl6_11)),
% 0.22/0.54    inference(subsumption_resolution,[],[f304,f137])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~spl6_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f135])).
% 0.22/0.54  fof(f304,plain,(
% 0.22/0.54    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_9),
% 0.22/0.54    inference(superposition,[],[f117,f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.54  fof(f117,plain,(
% 0.22/0.54    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | spl6_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f116])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    spl6_9 <=> r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.54  fof(f300,plain,(
% 0.22/0.54    ~spl6_8 | ~spl6_9),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f299])).
% 0.22/0.54  fof(f299,plain,(
% 0.22/0.54    $false | (~spl6_8 | ~spl6_9)),
% 0.22/0.54    inference(subsumption_resolution,[],[f295,f114])).
% 0.22/0.54  fof(f295,plain,(
% 0.22/0.54    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | ~spl6_9),
% 0.22/0.54    inference(subsumption_resolution,[],[f37,f118])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~spl6_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f116])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ~r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <~> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f15])).
% 0.22/0.54  fof(f15,conjecture,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => (r1_tarski(k7_relset_1(X0,X1,X2,X3),X4) <=> r1_tarski(X3,k8_relset_1(X0,X1,X2,X4))))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_14),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f293])).
% 0.22/0.54  fof(f293,plain,(
% 0.22/0.54    $false | (spl6_10 | ~spl6_11 | ~spl6_13 | ~spl6_14)),
% 0.22/0.54    inference(subsumption_resolution,[],[f290,f137])).
% 0.22/0.54  fof(f290,plain,(
% 0.22/0.54    ~r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (spl6_10 | ~spl6_13 | ~spl6_14)),
% 0.22/0.54    inference(resolution,[],[f240,f150])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    ( ! [X2] : (r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)) ) | ~spl6_13),
% 0.22/0.54    inference(avatar_component_clause,[],[f149])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    spl6_13 <=> ! [X2] : r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,X0),sK4) | ~r1_tarski(sK3,X0)) ) | (spl6_10 | ~spl6_14)),
% 0.22/0.54    inference(subsumption_resolution,[],[f236,f153])).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,X0),sK4) | ~r1_tarski(sK3,X0) | ~v1_relat_1(sK2)) ) | spl6_10),
% 0.22/0.54    inference(resolution,[],[f132,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(k9_relat_1(sK2,sK3),X0) | ~r1_tarski(X0,sK4)) ) | spl6_10),
% 0.22/0.54    inference(resolution,[],[f130,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.54  fof(f218,plain,(
% 0.22/0.54    ~spl6_7 | spl6_14),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f216])).
% 0.22/0.54  fof(f216,plain,(
% 0.22/0.54    $false | (~spl6_7 | spl6_14)),
% 0.22/0.54    inference(resolution,[],[f156,f108])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_14),
% 0.22/0.54    inference(resolution,[],[f154,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    ~v1_relat_1(sK2) | spl6_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f152])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    spl6_15 | ~spl6_17),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f199])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    $false | (spl6_15 | ~spl6_17)),
% 0.22/0.54    inference(subsumption_resolution,[],[f197,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f197,plain,(
% 0.22/0.54    ~r1_tarski(k1_xboole_0,sK5(k1_xboole_0)) | (spl6_15 | ~spl6_17)),
% 0.22/0.54    inference(superposition,[],[f164,f176])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | ~spl6_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f174])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl6_17 <=> k1_xboole_0 = sK1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK5(sK1)) | spl6_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f162])).
% 0.22/0.54  fof(f162,plain,(
% 0.22/0.54    spl6_15 <=> r1_tarski(sK1,sK5(sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    spl6_18 | ~spl6_7 | ~spl6_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f180,f170,f106,f183])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    spl6_16 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK2) | (~spl6_7 | ~spl6_16)),
% 0.22/0.54    inference(subsumption_resolution,[],[f178,f108])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_16),
% 0.22/0.54    inference(superposition,[],[f172,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f170])).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    spl6_16 | spl6_17 | ~spl6_6 | ~spl6_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f166,f106,f100,f174,f170])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    spl6_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl6_6 | ~spl6_7)),
% 0.22/0.54    inference(subsumption_resolution,[],[f104,f108])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_6),
% 0.22/0.54    inference(resolution,[],[f102,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    v1_funct_2(sK2,sK0,sK1) | ~spl6_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f100])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ~spl6_15 | spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f144,f76,f162])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl6_2 <=> v1_xboole_0(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK5(sK1)) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f110,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(sK5(X0),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~r1_tarski(sK1,X0)) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f87,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,sK1)) ) | spl6_2),
% 0.22/0.54    inference(resolution,[],[f78,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1) | spl6_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f76])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    spl6_13 | ~spl6_14 | ~spl6_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f86,f71,f152,f149])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X2] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(sK2,k10_relat_1(sK2,X2)),X2)) ) | ~spl6_1),
% 0.22/0.54    inference(resolution,[],[f73,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    spl6_11 | ~spl6_7 | ~spl6_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f126,f116,f106,f135])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | (~spl6_7 | ~spl6_9)),
% 0.22/0.54    inference(subsumption_resolution,[],[f125,f108])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    r1_tarski(sK3,k10_relat_1(sK2,sK4)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_9),
% 0.22/0.54    inference(superposition,[],[f118,f63])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ~spl6_10 | ~spl6_7 | spl6_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f124,f112,f106,f128])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | (~spl6_7 | spl6_8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f123,f108])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ~r1_tarski(k9_relat_1(sK2,sK3),sK4) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_8),
% 0.22/0.54    inference(superposition,[],[f113,f64])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    ~r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4) | spl6_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f112])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    spl6_8 | spl6_9),
% 0.22/0.54    inference(avatar_split_clause,[],[f36,f116,f112])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    r1_tarski(sK3,k8_relset_1(sK0,sK1,sK2,sK4)) | r1_tarski(k7_relset_1(sK0,sK1,sK2,sK3),sK4)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    spl6_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f42,f106])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    spl6_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f41,f100])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    spl6_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f39,f95])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ~spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f43,f76])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ~v1_xboole_0(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    spl6_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f40,f71])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (25284)------------------------------
% 0.22/0.54  % (25284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25284)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (25284)Memory used [KB]: 10746
% 0.22/0.54  % (25284)Time elapsed: 0.100 s
% 0.22/0.54  % (25284)------------------------------
% 0.22/0.54  % (25284)------------------------------
% 0.22/0.54  % (25280)Success in time 0.175 s
%------------------------------------------------------------------------------
