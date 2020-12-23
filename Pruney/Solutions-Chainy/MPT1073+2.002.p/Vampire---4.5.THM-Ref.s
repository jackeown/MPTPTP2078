%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 243 expanded)
%              Number of leaves         :   36 (  99 expanded)
%              Depth                    :    8
%              Number of atoms          :  402 ( 654 expanded)
%              Number of equality atoms :   61 (  98 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f607,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f85,f90,f95,f101,f120,f126,f180,f191,f200,f209,f236,f245,f249,f283,f320,f405,f518,f590,f603,f606])).

fof(f606,plain,
    ( ~ spl6_37
    | spl6_53 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | ~ spl6_37
    | spl6_53 ),
    inference(subsumption_resolution,[],[f604,f404])).

fof(f404,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl6_37
  <=> r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f604,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | spl6_53 ),
    inference(resolution,[],[f602,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f602,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | spl6_53 ),
    inference(avatar_component_clause,[],[f600])).

fof(f600,plain,
    ( spl6_53
  <=> m1_subset_1(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f603,plain,
    ( ~ spl6_53
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f596,f587,f600])).

fof(f587,plain,
    ( spl6_52
  <=> sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f596,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_52 ),
    inference(trivial_inequality_removal,[],[f595])).

fof(f595,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_52 ),
    inference(superposition,[],[f33,f589])).

fof(f589,plain,
    ( sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f587])).

fof(f33,plain,(
    ! [X4] :
      ( sK0 != k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(f590,plain,
    ( spl6_52
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f524,f515,f98,f71,f587])).

fof(f71,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f98,plain,
    ( spl6_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f515,plain,
    ( spl6_46
  <=> r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f524,plain,
    ( sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3))
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_46 ),
    inference(resolution,[],[f517,f134])).

fof(f134,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | k1_funct_1(sK3,X2) = X3 )
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f76,f100])).

fof(f100,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f76,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK3) )
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f73,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f517,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f515])).

fof(f518,plain,
    ( spl6_46
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f321,f317,f98,f515])).

fof(f317,plain,
    ( spl6_28
  <=> r2_hidden(sK0,k9_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f321,plain,
    ( r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3)
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(resolution,[],[f319,f106])).

fof(f106,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X3))
        | r2_hidden(k4_tarski(sK5(X2,X3,sK3),X2),sK3) )
    | ~ spl6_5 ),
    inference(resolution,[],[f100,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f319,plain,
    ( r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f317])).

fof(f405,plain,
    ( spl6_37
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f323,f317,f98,f402])).

fof(f323,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(resolution,[],[f319,f107])).

fof(f107,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X5))
        | r2_hidden(sK5(X4,X5,sK3),X5) )
    | ~ spl6_5 ),
    inference(resolution,[],[f100,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f320,plain,
    ( spl6_28
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f289,f280,f92,f317])).

fof(f92,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f280,plain,
    ( spl6_25
  <=> k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f289,plain,
    ( r2_hidden(sK0,k9_relat_1(sK3,sK1))
    | ~ spl6_4
    | ~ spl6_25 ),
    inference(superposition,[],[f94,f282])).

fof(f282,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f280])).

fof(f94,plain,
    ( r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f283,plain,
    ( spl6_25
    | ~ spl6_3
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f258,f233,f87,f280])).

fof(f87,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f233,plain,
    ( spl6_23
  <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f258,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ spl6_3
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f255,f89])).

fof(f89,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f255,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_23 ),
    inference(superposition,[],[f235,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f235,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f233])).

fof(f249,plain,
    ( ~ spl6_11
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl6_11
    | spl6_19 ),
    inference(subsumption_resolution,[],[f212,f147])).

fof(f147,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f212,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl6_19 ),
    inference(forward_demodulation,[],[f211,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f211,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | spl6_19 ),
    inference(resolution,[],[f208,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f208,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl6_19
  <=> v5_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f245,plain,
    ( ~ spl6_3
    | spl6_11
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl6_3
    | spl6_11
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f243,f148])).

fof(f148,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f146])).

fof(f243,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f238,f66])).

fof(f238,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_3
    | ~ spl6_18 ),
    inference(superposition,[],[f89,f199])).

fof(f199,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_18
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f236,plain,
    ( spl6_23
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f204,f193,f87,f233])).

fof(f193,plain,
    ( spl6_17
  <=> sK1 = k8_relset_1(sK1,sK2,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f204,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f203,f89])).

fof(f203,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_17 ),
    inference(superposition,[],[f58,f195])).

fof(f195,plain,
    ( sK1 = k8_relset_1(sK1,sK2,sK3,sK2)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f209,plain,
    ( ~ spl6_19
    | ~ spl6_5
    | spl6_16 ),
    inference(avatar_split_clause,[],[f201,f188,f98,f206])).

fof(f188,plain,
    ( spl6_16
  <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f201,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ spl6_5
    | spl6_16 ),
    inference(resolution,[],[f190,f110])).

fof(f110,plain,
    ( ! [X10] :
        ( r1_tarski(k2_relat_1(sK3),X10)
        | ~ v5_relat_1(sK3,X10) )
    | ~ spl6_5 ),
    inference(resolution,[],[f100,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f190,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f188])).

fof(f200,plain,
    ( spl6_17
    | spl6_18
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f153,f87,f82,f71,f197,f193])).

fof(f82,plain,
    ( spl6_2
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f153,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k8_relset_1(sK1,sK2,sK3,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f152,f89])).

fof(f152,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_xboole_0 = sK2
    | sK1 = k8_relset_1(sK1,sK2,sK3,sK2)
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f78,f84])).

fof(f84,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f78,plain,
    ( ! [X6,X5] :
        ( ~ v1_funct_2(sK3,X5,X6)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k1_xboole_0 = X6
        | k8_relset_1(X5,X6,sK3,X6) = X5 )
    | ~ spl6_1 ),
    inference(resolution,[],[f73,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

fof(f191,plain,
    ( ~ spl6_16
    | spl6_15 ),
    inference(avatar_split_clause,[],[f185,f177,f188])).

fof(f177,plain,
    ( spl6_15
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f185,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | spl6_15 ),
    inference(resolution,[],[f179,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f179,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f180,plain,
    ( ~ spl6_15
    | spl6_8 ),
    inference(avatar_split_clause,[],[f175,f123,f177])).

fof(f123,plain,
    ( spl6_8
  <=> v1_xboole_0(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f175,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))
    | spl6_8 ),
    inference(forward_demodulation,[],[f172,f66])).

fof(f172,plain,
    ( ! [X0] : ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | spl6_8 ),
    inference(resolution,[],[f131,f38])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | spl6_8 ),
    inference(resolution,[],[f125,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f125,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( ~ spl6_8
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f121,f117,f123])).

fof(f117,plain,
    ( spl6_7
  <=> r2_hidden(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f121,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | ~ spl6_7 ),
    inference(resolution,[],[f119,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f119,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f120,plain,
    ( spl6_7
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f104,f92,f87,f117])).

fof(f104,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f103,f89])).

fof(f103,plain,
    ( r2_hidden(sK0,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_4 ),
    inference(superposition,[],[f94,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f101,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f96,f87,f98])).

fof(f96,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_3 ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
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

fof(f95,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f37,f92])).

fof(f37,plain,(
    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f36,f87])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f35,f82])).

fof(f35,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (30613)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (30610)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (30624)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (30613)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f607,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f74,f85,f90,f95,f101,f120,f126,f180,f191,f200,f209,f236,f245,f249,f283,f320,f405,f518,f590,f603,f606])).
% 0.22/0.51  fof(f606,plain,(
% 0.22/0.51    ~spl6_37 | spl6_53),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f605])).
% 0.22/0.51  fof(f605,plain,(
% 0.22/0.51    $false | (~spl6_37 | spl6_53)),
% 0.22/0.51    inference(subsumption_resolution,[],[f604,f404])).
% 0.22/0.51  fof(f404,plain,(
% 0.22/0.51    r2_hidden(sK5(sK0,sK1,sK3),sK1) | ~spl6_37),
% 0.22/0.51    inference(avatar_component_clause,[],[f402])).
% 0.22/0.51  fof(f402,plain,(
% 0.22/0.51    spl6_37 <=> r2_hidden(sK5(sK0,sK1,sK3),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.22/0.51  fof(f604,plain,(
% 0.22/0.51    ~r2_hidden(sK5(sK0,sK1,sK3),sK1) | spl6_53),
% 0.22/0.51    inference(resolution,[],[f602,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.51  fof(f602,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK3),sK1) | spl6_53),
% 0.22/0.51    inference(avatar_component_clause,[],[f600])).
% 0.22/0.51  fof(f600,plain,(
% 0.22/0.51    spl6_53 <=> m1_subset_1(sK5(sK0,sK1,sK3),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.22/0.51  fof(f603,plain,(
% 0.22/0.51    ~spl6_53 | ~spl6_52),
% 0.22/0.51    inference(avatar_split_clause,[],[f596,f587,f600])).
% 0.22/0.51  fof(f587,plain,(
% 0.22/0.51    spl6_52 <=> sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.22/0.51  fof(f596,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0,sK1,sK3),sK1) | ~spl6_52),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f595])).
% 0.22/0.51  fof(f595,plain,(
% 0.22/0.51    sK0 != sK0 | ~m1_subset_1(sK5(sK0,sK1,sK3),sK1) | ~spl6_52),
% 0.22/0.51    inference(superposition,[],[f33,f589])).
% 0.22/0.51  fof(f589,plain,(
% 0.22/0.51    sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3)) | ~spl6_52),
% 0.22/0.51    inference(avatar_component_clause,[],[f587])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X4] : (sK0 != k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.51    inference(negated_conjecture,[],[f16])).
% 0.22/0.51  fof(f16,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).
% 0.22/0.51  fof(f590,plain,(
% 0.22/0.51    spl6_52 | ~spl6_1 | ~spl6_5 | ~spl6_46),
% 0.22/0.51    inference(avatar_split_clause,[],[f524,f515,f98,f71,f587])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    spl6_1 <=> v1_funct_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl6_5 <=> v1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.51  fof(f515,plain,(
% 0.22/0.51    spl6_46 <=> r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.22/0.51  fof(f524,plain,(
% 0.22/0.51    sK0 = k1_funct_1(sK3,sK5(sK0,sK1,sK3)) | (~spl6_1 | ~spl6_5 | ~spl6_46)),
% 0.22/0.51    inference(resolution,[],[f517,f134])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | k1_funct_1(sK3,X2) = X3) ) | (~spl6_1 | ~spl6_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f76,f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    v1_relat_1(sK3) | ~spl6_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f98])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~v1_relat_1(sK3) | k1_funct_1(sK3,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK3)) ) | ~spl6_1),
% 0.22/0.51    inference(resolution,[],[f73,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    v1_funct_1(sK3) | ~spl6_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f71])).
% 0.22/0.51  fof(f517,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3) | ~spl6_46),
% 0.22/0.51    inference(avatar_component_clause,[],[f515])).
% 0.22/0.51  fof(f518,plain,(
% 0.22/0.51    spl6_46 | ~spl6_5 | ~spl6_28),
% 0.22/0.51    inference(avatar_split_clause,[],[f321,f317,f98,f515])).
% 0.22/0.51  fof(f317,plain,(
% 0.22/0.51    spl6_28 <=> r2_hidden(sK0,k9_relat_1(sK3,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.51  fof(f321,plain,(
% 0.22/0.51    r2_hidden(k4_tarski(sK5(sK0,sK1,sK3),sK0),sK3) | (~spl6_5 | ~spl6_28)),
% 0.22/0.51    inference(resolution,[],[f319,f106])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r2_hidden(X2,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X2,X3,sK3),X2),sK3)) ) | ~spl6_5),
% 0.22/0.51    inference(resolution,[],[f100,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.51  fof(f319,plain,(
% 0.22/0.51    r2_hidden(sK0,k9_relat_1(sK3,sK1)) | ~spl6_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f317])).
% 0.22/0.51  fof(f405,plain,(
% 0.22/0.51    spl6_37 | ~spl6_5 | ~spl6_28),
% 0.22/0.51    inference(avatar_split_clause,[],[f323,f317,f98,f402])).
% 0.22/0.51  fof(f323,plain,(
% 0.22/0.51    r2_hidden(sK5(sK0,sK1,sK3),sK1) | (~spl6_5 | ~spl6_28)),
% 0.22/0.51    inference(resolution,[],[f319,f107])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    ( ! [X4,X5] : (~r2_hidden(X4,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X4,X5,sK3),X5)) ) | ~spl6_5),
% 0.22/0.51    inference(resolution,[],[f100,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f320,plain,(
% 0.22/0.51    spl6_28 | ~spl6_4 | ~spl6_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f289,f280,f92,f317])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl6_4 <=> r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    spl6_25 <=> k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    r2_hidden(sK0,k9_relat_1(sK3,sK1)) | (~spl6_4 | ~spl6_25)),
% 0.22/0.51    inference(superposition,[],[f94,f282])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | ~spl6_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f280])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3)) | ~spl6_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f92])).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    spl6_25 | ~spl6_3 | ~spl6_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f258,f233,f87,f280])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    spl6_23 <=> k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | (~spl6_3 | ~spl6_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f255,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f87])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    k2_relset_1(sK1,sK2,sK3) = k9_relat_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_23),
% 0.22/0.51    inference(superposition,[],[f235,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~spl6_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f233])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    ~spl6_11 | spl6_19),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f248])).
% 0.22/0.51  fof(f248,plain,(
% 0.22/0.51    $false | (~spl6_11 | spl6_19)),
% 0.22/0.51    inference(subsumption_resolution,[],[f212,f147])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f146,plain,(
% 0.22/0.51    spl6_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl6_19),
% 0.22/0.51    inference(forward_demodulation,[],[f211,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | spl6_19),
% 0.22/0.51    inference(resolution,[],[f208,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    ~v5_relat_1(sK3,k1_xboole_0) | spl6_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f206])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    spl6_19 <=> v5_relat_1(sK3,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    ~spl6_3 | spl6_11 | ~spl6_18),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f244])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    $false | (~spl6_3 | spl6_11 | ~spl6_18)),
% 0.22/0.51    inference(subsumption_resolution,[],[f243,f148])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl6_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f146])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | ~spl6_18)),
% 0.22/0.51    inference(forward_demodulation,[],[f238,f66])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl6_3 | ~spl6_18)),
% 0.22/0.51    inference(superposition,[],[f89,f199])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | ~spl6_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f197])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    spl6_18 <=> k1_xboole_0 = sK2),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    spl6_23 | ~spl6_3 | ~spl6_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f204,f193,f87,f233])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    spl6_17 <=> sK1 = k8_relset_1(sK1,sK2,sK3,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | (~spl6_3 | ~spl6_17)),
% 0.22/0.51    inference(subsumption_resolution,[],[f203,f89])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    k2_relset_1(sK1,sK2,sK3) = k7_relset_1(sK1,sK2,sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_17),
% 0.22/0.51    inference(superposition,[],[f58,f195])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    sK1 = k8_relset_1(sK1,sK2,sK3,sK2) | ~spl6_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f193])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    ~spl6_19 | ~spl6_5 | spl6_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f201,f188,f98,f206])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    spl6_16 <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ~v5_relat_1(sK3,k1_xboole_0) | (~spl6_5 | spl6_16)),
% 0.22/0.51    inference(resolution,[],[f190,f110])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ( ! [X10] : (r1_tarski(k2_relat_1(sK3),X10) | ~v5_relat_1(sK3,X10)) ) | ~spl6_5),
% 0.22/0.51    inference(resolution,[],[f100,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f188])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    spl6_17 | spl6_18 | ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f153,f87,f82,f71,f197,f193])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl6_2 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    k1_xboole_0 = sK2 | sK1 = k8_relset_1(sK1,sK2,sK3,sK2) | (~spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f152,f89])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_xboole_0 = sK2 | sK1 = k8_relset_1(sK1,sK2,sK3,sK2) | (~spl6_1 | ~spl6_2)),
% 0.22/0.51    inference(resolution,[],[f78,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK1,sK2) | ~spl6_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f82])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X6,X5] : (~v1_funct_2(sK3,X5,X6) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k1_xboole_0 = X6 | k8_relset_1(X5,X6,sK3,X6) = X5) ) | ~spl6_1),
% 0.22/0.51    inference(resolution,[],[f73,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ~spl6_16 | spl6_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f185,f177,f188])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    spl6_15 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | spl6_15),
% 0.22/0.51    inference(resolution,[],[f179,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f179,plain,(
% 0.22/0.51    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) | spl6_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f177])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ~spl6_15 | spl6_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f175,f123,f177])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl6_8 <=> v1_xboole_0(k2_relat_1(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k1_xboole_0)) | spl6_8),
% 0.22/0.51    inference(forward_demodulation,[],[f172,f66])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | spl6_8),
% 0.22/0.51    inference(resolution,[],[f131,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_8),
% 0.22/0.51    inference(resolution,[],[f125,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_relat_1(sK3)) | spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f123])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ~spl6_8 | ~spl6_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f121,f117,f123])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl6_7 <=> r2_hidden(sK0,k2_relat_1(sK3))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ~v1_xboole_0(k2_relat_1(sK3)) | ~spl6_7),
% 0.22/0.51    inference(resolution,[],[f119,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_relat_1(sK3)) | ~spl6_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    spl6_7 | ~spl6_3 | ~spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f104,f92,f87,f117])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_relat_1(sK3)) | (~spl6_3 | ~spl6_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f103,f89])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_4),
% 0.22/0.51    inference(superposition,[],[f94,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    spl6_5 | ~spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f96,f87,f98])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    v1_relat_1(sK3) | ~spl6_3),
% 0.22/0.51    inference(resolution,[],[f89,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f37,f92])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    r2_hidden(sK0,k2_relset_1(sK1,sK2,sK3))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f36,f87])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f35,f82])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f34,f71])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    v1_funct_1(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (30613)------------------------------
% 0.22/0.51  % (30613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30613)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (30613)Memory used [KB]: 11001
% 0.22/0.51  % (30613)Time elapsed: 0.072 s
% 0.22/0.51  % (30613)------------------------------
% 0.22/0.51  % (30613)------------------------------
% 0.22/0.51  % (30609)Success in time 0.147 s
%------------------------------------------------------------------------------
