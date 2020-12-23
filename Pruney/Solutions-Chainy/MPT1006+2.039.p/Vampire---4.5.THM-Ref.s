%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 153 expanded)
%              Number of leaves         :   30 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  268 ( 383 expanded)
%              Number of equality atoms :   53 (  83 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f73,f85,f90,f94,f100,f104,f108,f116,f125,f137,f148,f165,f169,f174,f183])).

fof(f183,plain,
    ( ~ spl4_14
    | spl4_23
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl4_14
    | spl4_23
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f177,f168])).

fof(f168,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_27
  <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f177,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ spl4_14
    | spl4_23
    | ~ spl4_28 ),
    inference(backward_demodulation,[],[f147,f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_14
    | ~ spl4_28 ),
    inference(resolution,[],[f173,f99])).

fof(f99,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_14
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK3(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f173,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_28
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f147,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_23
  <=> k1_xboole_0 = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f174,plain,
    ( spl4_28
    | ~ spl4_3
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f170,f163,f51,f172])).

fof(f51,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f163,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f170,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_3
    | ~ spl4_26 ),
    inference(resolution,[],[f164,f52])).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f164,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f169,plain,
    ( spl4_27
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f130,f123,f92,f167])).

fof(f92,plain,
    ( spl4_13
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f123,plain,
    ( spl4_19
  <=> ! [X2] : r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f130,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(resolution,[],[f124,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f124,plain,
    ( ! [X2] : r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f123])).

fof(f165,plain,
    ( spl4_26
    | ~ spl4_4
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f121,f114,f55,f163])).

fof(f55,plain,
    ( spl4_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f114,plain,
    ( spl4_18
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_4
    | ~ spl4_18 ),
    inference(resolution,[],[f115,f56])).

fof(f56,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f115,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f114])).

fof(f148,plain,
    ( ~ spl4_23
    | ~ spl4_3
    | spl4_5
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f144,f135,f83,f59,f51,f146])).

fof(f59,plain,
    ( spl4_5
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f83,plain,
    ( spl4_11
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f135,plain,
    ( spl4_21
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f144,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ spl4_3
    | spl4_5
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f143,f52])).

fof(f143,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(sK2,sK1)
    | spl4_5
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f142,f84])).

fof(f84,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f142,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_5
    | ~ spl4_21 ),
    inference(superposition,[],[f60,f136])).

fof(f136,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f135])).

fof(f60,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f137,plain,(
    spl4_21 ),
    inference(avatar_split_clause,[],[f38,f135])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f125,plain,
    ( spl4_19
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f120,f106,f102,f88,f123])).

fof(f88,plain,
    ( spl4_12
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f102,plain,
    ( spl4_15
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f106,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f120,plain,
    ( ! [X2] : r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f118,f89])).

fof(f89,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f88])).

fof(f118,plain,
    ( ! [X2] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_15
    | ~ spl4_16 ),
    inference(superposition,[],[f107,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f116,plain,(
    spl4_18 ),
    inference(avatar_split_clause,[],[f37,f114])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f108,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f33,f106])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f104,plain,
    ( spl4_15
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f95,f71,f67,f102])).

fof(f67,plain,
    ( spl4_7
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f71,plain,
    ( spl4_8
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f95,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(superposition,[],[f72,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f72,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f100,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f32,f98])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f94,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f30,f92])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f90,plain,
    ( spl4_12
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f86,f67,f63,f88])).

fof(f63,plain,
    ( spl4_6
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f86,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(superposition,[],[f64,f68])).

fof(f64,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f85,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f40,f83])).

fof(f40,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f73,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f69,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f65,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f61,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(f57,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f53,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f41,f51])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f23,f40])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:53:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (25602)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (25611)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (25602)Refutation not found, incomplete strategy% (25602)------------------------------
% 0.21/0.46  % (25602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (25602)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (25602)Memory used [KB]: 10618
% 0.21/0.46  % (25602)Time elapsed: 0.063 s
% 0.21/0.46  % (25602)------------------------------
% 0.21/0.46  % (25602)------------------------------
% 0.21/0.47  % (25611)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f73,f85,f90,f94,f100,f104,f108,f116,f125,f137,f148,f165,f169,f174,f183])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    ~spl4_14 | spl4_23 | ~spl4_27 | ~spl4_28),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f182])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    $false | (~spl4_14 | spl4_23 | ~spl4_27 | ~spl4_28)),
% 0.21/0.47    inference(subsumption_resolution,[],[f177,f168])).
% 0.21/0.47  fof(f168,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | ~spl4_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f167])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    spl4_27 <=> ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | (~spl4_14 | spl4_23 | ~spl4_28)),
% 0.21/0.47    inference(backward_demodulation,[],[f147,f175])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | (~spl4_14 | ~spl4_28)),
% 0.21/0.47    inference(resolution,[],[f173,f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl4_14 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl4_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f172])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    spl4_28 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    k1_xboole_0 != k10_relat_1(sK2,sK1) | spl4_23),
% 0.21/0.47    inference(avatar_component_clause,[],[f146])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    spl4_23 <=> k1_xboole_0 = k10_relat_1(sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    spl4_28 | ~spl4_3 | ~spl4_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f170,f163,f51,f172])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    spl4_26 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | (~spl4_3 | ~spl4_26)),
% 0.21/0.47    inference(resolution,[],[f164,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f51])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | ~spl4_26),
% 0.21/0.47    inference(avatar_component_clause,[],[f163])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    spl4_27 | ~spl4_13 | ~spl4_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f130,f123,f92,f167])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl4_13 <=> ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    spl4_19 <=> ! [X2] : r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl4_13 | ~spl4_19)),
% 0.21/0.47    inference(resolution,[],[f124,f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X2] : (r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)) ) | ~spl4_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f123])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    spl4_26 | ~spl4_4 | ~spl4_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f121,f114,f55,f163])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl4_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl4_18 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) ) | (~spl4_4 | ~spl4_18)),
% 0.21/0.47    inference(resolution,[],[f115,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0) | ~spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl4_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f114])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ~spl4_23 | ~spl4_3 | spl4_5 | ~spl4_11 | ~spl4_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f144,f135,f83,f59,f51,f146])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl4_5 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl4_11 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl4_21 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    k1_xboole_0 != k10_relat_1(sK2,sK1) | (~spl4_3 | spl4_5 | ~spl4_11 | ~spl4_21)),
% 0.21/0.47    inference(subsumption_resolution,[],[f143,f52])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(sK2,sK1) | (spl4_5 | ~spl4_11 | ~spl4_21)),
% 0.21/0.47    inference(forward_demodulation,[],[f142,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl4_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f83])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    k1_xboole_0 != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_5 | ~spl4_21)),
% 0.21/0.47    inference(superposition,[],[f60,f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f135])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    spl4_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f135])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    spl4_19 | ~spl4_12 | ~spl4_15 | ~spl4_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f120,f106,f102,f88,f123])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl4_12 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl4_15 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl4_16 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X2] : (r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)) ) | (~spl4_12 | ~spl4_15 | ~spl4_16)),
% 0.21/0.47    inference(subsumption_resolution,[],[f118,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    v1_relat_1(k1_xboole_0) | ~spl4_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X2] : (r1_tarski(k10_relat_1(k1_xboole_0,X2),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_15 | ~spl4_16)),
% 0.21/0.47    inference(superposition,[],[f107,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f102])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl4_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f106])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl4_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f114])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl4_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f106])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl4_15 | ~spl4_7 | ~spl4_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f95,f71,f67,f102])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl4_7 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl4_8 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_7 | ~spl4_8)),
% 0.21/0.47    inference(superposition,[],[f72,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl4_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl4_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl4_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f98])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f92])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl4_12 | ~spl4_6 | ~spl4_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f67,f63,f88])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl4_6 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    v1_relat_1(k1_xboole_0) | (~spl4_6 | ~spl4_7)),
% 0.21/0.47    inference(superposition,[],[f64,f68])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl4_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl4_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f83])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl4_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f71])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl4_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f67])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f63])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ~spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f59])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f11])).
% 0.21/0.47  fof(f11,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f55])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f51])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.47    inference(backward_demodulation,[],[f23,f40])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (25611)------------------------------
% 0.21/0.47  % (25611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25611)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (25611)Memory used [KB]: 10618
% 0.21/0.47  % (25611)Time elapsed: 0.070 s
% 0.21/0.47  % (25611)------------------------------
% 0.21/0.47  % (25611)------------------------------
% 0.21/0.47  % (25598)Success in time 0.11 s
%------------------------------------------------------------------------------
