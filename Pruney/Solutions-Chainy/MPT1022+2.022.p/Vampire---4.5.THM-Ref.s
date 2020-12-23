%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 308 expanded)
%              Number of leaves         :   40 ( 134 expanded)
%              Depth                    :   10
%              Number of atoms          :  491 ( 984 expanded)
%              Number of equality atoms :  102 ( 218 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f106,f112,f115,f120,f125,f132,f140,f143,f153,f160,f174,f182,f188,f212,f222,f239,f244,f247,f250])).

fof(f250,plain,
    ( ~ spl3_5
    | ~ spl3_4
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f249,f242,f79,f83])).

fof(f83,plain,
    ( spl3_5
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f79,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f242,plain,
    ( spl3_30
  <=> ! [X1,X0] :
        ( ~ v3_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f249,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ spl3_4
    | ~ spl3_30 ),
    inference(resolution,[],[f243,f80])).

fof(f80,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v3_funct_2(sK2,X0,X1) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f242])).

fof(f247,plain,
    ( spl3_21
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f245,f237,f75,f186])).

fof(f186,plain,
    ( spl3_21
  <=> sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f75,plain,
    ( spl3_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f237,plain,
    ( spl3_29
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f245,plain,
    ( sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(resolution,[],[f238,f76])).

fof(f76,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f237])).

fof(f244,plain,
    ( ~ spl3_7
    | spl3_30
    | spl3_28 ),
    inference(avatar_split_clause,[],[f240,f234,f242,f91])).

fof(f91,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f234,plain,
    ( spl3_28
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f240,plain,
    ( ! [X0,X1] :
        ( ~ v3_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | spl3_28 ),
    inference(resolution,[],[f235,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f235,plain,
    ( ~ v2_funct_1(sK2)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f234])).

fof(f239,plain,
    ( ~ spl3_9
    | ~ spl3_7
    | ~ spl3_28
    | spl3_29
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f232,f219,f237,f234,f91,f104])).

fof(f104,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f219,plain,
    ( spl3_24
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ v2_funct_1(sK2)
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_24 ),
    inference(superposition,[],[f53,f220])).

fof(f220,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f222,plain,
    ( ~ spl3_7
    | ~ spl3_6
    | ~ spl3_4
    | spl3_24
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f214,f210,f219,f79,f87,f91])).

fof(f87,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f210,plain,
    ( spl3_23
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f214,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_23 ),
    inference(superposition,[],[f51,f211])).

fof(f211,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f210])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f212,plain,
    ( spl3_23
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f208,f151,f138,f118,f79,f210])).

fof(f118,plain,
    ( spl3_11
  <=> k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f138,plain,
    ( spl3_15
  <=> sK0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f151,plain,
    ( spl3_17
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f208,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f207,f152])).

fof(f152,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f207,plain,
    ( k10_relat_1(sK2,sK0) = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f206,f139])).

fof(f139,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f206,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f205,f163])).

fof(f163,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)
    | ~ spl3_4 ),
    inference(resolution,[],[f64,f80])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f205,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k8_relset_1(sK0,sK0,sK2,k2_relat_1(sK2))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f204,f119])).

fof(f119,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f204,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK0))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f203,f169])).

fof(f169,plain,
    ( ! [X0] : k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0)
    | ~ spl3_4 ),
    inference(resolution,[],[f65,f80])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f203,plain,
    ( k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK0)) = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f60,f80])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f188,plain,
    ( ~ spl3_21
    | ~ spl3_4
    | spl3_20 ),
    inference(avatar_split_clause,[],[f184,f180,f79,f186])).

fof(f180,plain,
    ( spl3_20
  <=> sK1 = k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f184,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | ~ spl3_4
    | spl3_20 ),
    inference(superposition,[],[f181,f163])).

fof(f181,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( ~ spl3_20
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f178,f79,f71,f180])).

fof(f71,plain,
    ( spl3_2
  <=> sK1 = k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f178,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f72,f169])).

fof(f72,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f174,plain,
    ( ~ spl3_18
    | spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f172,f79,f68,f158])).

fof(f158,plain,
    ( spl3_18
  <=> sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f68,plain,
    ( spl3_1
  <=> sK1 = k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f172,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f170,f163])).

fof(f170,plain,
    ( sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_4 ),
    inference(superposition,[],[f69,f169])).

fof(f69,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f160,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f156,f138,f123,f75,f158])).

fof(f123,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f156,plain,
    ( sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | ~ spl3_3
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(resolution,[],[f147,f76])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_12
    | ~ spl3_15 ),
    inference(superposition,[],[f124,f139])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f153,plain,
    ( ~ spl3_9
    | spl3_17
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f149,f138,f151,f104])).

fof(f149,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_15 ),
    inference(superposition,[],[f47,f139])).

fof(f47,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f143,plain,
    ( ~ spl3_4
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl3_4
    | spl3_14 ),
    inference(subsumption_resolution,[],[f80,f141])).

fof(f141,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl3_14 ),
    inference(resolution,[],[f136,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f136,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl3_14
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f140,plain,
    ( ~ spl3_9
    | ~ spl3_14
    | spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f133,f130,f138,f135,f104])).

fof(f130,plain,
    ( spl3_13
  <=> v2_funct_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f133,plain,
    ( sK0 = k2_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f131,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f131,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f132,plain,
    ( ~ spl3_5
    | spl3_13
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f127,f91,f79,f130,f83])).

fof(f127,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ v3_funct_2(sK2,sK0,sK0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f126,f80])).

fof(f126,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v2_funct_2(sK2,X1)
        | ~ v3_funct_2(sK2,X0,X1) )
    | ~ spl3_7 ),
    inference(resolution,[],[f63,f92])).

fof(f92,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f125,plain,
    ( ~ spl3_9
    | spl3_12
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f121,f91,f123,f104])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl3_7 ),
    inference(resolution,[],[f52,f92])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

% (29703)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (29711)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f120,plain,
    ( ~ spl3_9
    | spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f116,f101,f118,f104])).

fof(f101,plain,
    ( spl3_8
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f116,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f50,f102])).

fof(f102,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f115,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f111,f49])).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f111,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_10
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f112,plain,
    ( ~ spl3_10
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_split_clause,[],[f108,f104,f79,f110])).

fof(f108,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl3_4
    | spl3_9 ),
    inference(resolution,[],[f107,f80])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_9 ),
    inference(resolution,[],[f105,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f105,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f99,f79,f104,f101])).

fof(f99,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f95,f80])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0)
      | k7_relat_1(X0,X1) = X0 ) ),
    inference(resolution,[],[f54,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f93,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f41,f91])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
      | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
    & r1_tarski(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2] :
        ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
          | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
        & r1_tarski(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
   => ( ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
        | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) )
      & r1_tarski(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

fof(f89,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f43,f83])).

fof(f43,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f44,f79])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f45,f75])).

fof(f45,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f46,f71,f68])).

fof(f46,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (29701)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (29701)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (29709)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f73,f77,f81,f85,f89,f93,f106,f112,f115,f120,f125,f132,f140,f143,f153,f160,f174,f182,f188,f212,f222,f239,f244,f247,f250])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    ~spl3_5 | ~spl3_4 | ~spl3_30),
% 0.20/0.47    inference(avatar_split_clause,[],[f249,f242,f79,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl3_5 <=> v3_funct_2(sK2,sK0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    spl3_30 <=> ! [X1,X0] : (~v3_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.47  fof(f249,plain,(
% 0.20/0.47    ~v3_funct_2(sK2,sK0,sK0) | (~spl3_4 | ~spl3_30)),
% 0.20/0.47    inference(resolution,[],[f243,f80])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f79])).
% 0.20/0.47  fof(f243,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(sK2,X0,X1)) ) | ~spl3_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f242])).
% 0.20/0.47  fof(f247,plain,(
% 0.20/0.47    spl3_21 | ~spl3_3 | ~spl3_29),
% 0.20/0.47    inference(avatar_split_clause,[],[f245,f237,f75,f186])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    spl3_21 <=> sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl3_3 <=> r1_tarski(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    spl3_29 <=> ! [X0] : (~r1_tarski(X0,sK0) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    sK1 = k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | (~spl3_3 | ~spl3_29)),
% 0.20/0.47    inference(resolution,[],[f238,f76])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    r1_tarski(sK1,sK0) | ~spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f75])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,sK0) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0) ) | ~spl3_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f237])).
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    ~spl3_7 | spl3_30 | spl3_28),
% 0.20/0.47    inference(avatar_split_clause,[],[f240,f234,f242,f91])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl3_7 <=> v1_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f234,plain,(
% 0.20/0.47    spl3_28 <=> v2_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v3_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_28),
% 0.20/0.47    inference(resolution,[],[f235,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).
% 0.20/0.47  fof(f235,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | spl3_28),
% 0.20/0.47    inference(avatar_component_clause,[],[f234])).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    ~spl3_9 | ~spl3_7 | ~spl3_28 | spl3_29 | ~spl3_24),
% 0.20/0.47    inference(avatar_split_clause,[],[f232,f219,f237,f234,f91,f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl3_9 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f219,plain,(
% 0.20/0.47    spl3_24 <=> sK0 = k1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.47  fof(f232,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v2_funct_1(sK2) | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl3_24),
% 0.20/0.47    inference(superposition,[],[f53,f220])).
% 0.20/0.47  fof(f220,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK2) | ~spl3_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f219])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    ~spl3_7 | ~spl3_6 | ~spl3_4 | spl3_24 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f214,f210,f219,f79,f87,f91])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    spl3_6 <=> v1_funct_2(sK2,sK0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f210,plain,(
% 0.20/0.47    spl3_23 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~spl3_23),
% 0.20/0.47    inference(superposition,[],[f51,f211])).
% 0.20/0.47  fof(f211,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) | ~spl3_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f210])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    spl3_23 | ~spl3_4 | ~spl3_11 | ~spl3_15 | ~spl3_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f208,f151,f138,f118,f79,f210])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl3_11 <=> k9_relat_1(sK2,sK0) = k2_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    spl3_15 <=> sK0 = k2_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    spl3_17 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) | (~spl3_4 | ~spl3_11 | ~spl3_15 | ~spl3_17)),
% 0.20/0.47    inference(forward_demodulation,[],[f207,f152])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | ~spl3_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f151])).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    k10_relat_1(sK2,sK0) = k1_relset_1(sK0,sK0,sK2) | (~spl3_4 | ~spl3_11 | ~spl3_15)),
% 0.20/0.47    inference(forward_demodulation,[],[f206,f139])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    sK0 = k2_relat_1(sK2) | ~spl3_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f138])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relset_1(sK0,sK0,sK2) | (~spl3_4 | ~spl3_11)),
% 0.20/0.47    inference(forward_demodulation,[],[f205,f163])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK0,sK2,X0)) ) | ~spl3_4),
% 0.20/0.47    inference(resolution,[],[f64,f80])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    k1_relset_1(sK0,sK0,sK2) = k8_relset_1(sK0,sK0,sK2,k2_relat_1(sK2)) | (~spl3_4 | ~spl3_11)),
% 0.20/0.47    inference(forward_demodulation,[],[f204,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    k9_relat_1(sK2,sK0) = k2_relat_1(sK2) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f118])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    k1_relset_1(sK0,sK0,sK2) = k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK0)) | ~spl3_4),
% 0.20/0.47    inference(forward_demodulation,[],[f203,f169])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    ( ! [X0] : (k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0)) ) | ~spl3_4),
% 0.20/0.47    inference(resolution,[],[f65,f80])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK0)) = k1_relset_1(sK0,sK0,sK2) | ~spl3_4),
% 0.20/0.47    inference(resolution,[],[f60,f80])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    ~spl3_21 | ~spl3_4 | spl3_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f184,f180,f79,f186])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    spl3_20 <=> sK1 = k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) | (~spl3_4 | spl3_20)),
% 0.20/0.47    inference(superposition,[],[f181,f163])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | spl3_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f180])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ~spl3_20 | spl3_2 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f178,f79,f71,f180])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl3_2 <=> sK1 = k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1)) | (spl3_2 | ~spl3_4)),
% 0.20/0.47    inference(forward_demodulation,[],[f72,f169])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    ~spl3_18 | spl3_1 | ~spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f172,f79,f68,f158])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    spl3_18 <=> sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl3_1 <=> sK1 = k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | (spl3_1 | ~spl3_4)),
% 0.20/0.48    inference(forward_demodulation,[],[f170,f163])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | (spl3_1 | ~spl3_4)),
% 0.20/0.48    inference(superposition,[],[f69,f169])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1)) | spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f68])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    spl3_18 | ~spl3_3 | ~spl3_12 | ~spl3_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f156,f138,f123,f75,f158])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl3_12 <=> ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) | (~spl3_3 | ~spl3_12 | ~spl3_15)),
% 0.20/0.48    inference(resolution,[],[f147,f76])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,sK0) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | (~spl3_12 | ~spl3_15)),
% 0.20/0.48    inference(superposition,[],[f124,f139])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0) ) | ~spl3_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ~spl3_9 | spl3_17 | ~spl3_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f149,f138,f151,f104])).
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    k1_relat_1(sK2) = k10_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~spl3_15),
% 0.20/0.48    inference(superposition,[],[f47,f139])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    ~spl3_4 | spl3_14),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f142])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    $false | (~spl3_4 | spl3_14)),
% 0.20/0.48    inference(subsumption_resolution,[],[f80,f141])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl3_14),
% 0.20/0.48    inference(resolution,[],[f136,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    ~v5_relat_1(sK2,sK0) | spl3_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f135])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    spl3_14 <=> v5_relat_1(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ~spl3_9 | ~spl3_14 | spl3_15 | ~spl3_13),
% 0.20/0.48    inference(avatar_split_clause,[],[f133,f130,f138,f135,f104])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    spl3_13 <=> v2_funct_2(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    sK0 = k2_relat_1(sK2) | ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~spl3_13),
% 0.20/0.48    inference(resolution,[],[f131,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v2_funct_2(X1,X0) | k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    v2_funct_2(sK2,sK0) | ~spl3_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f130])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ~spl3_5 | spl3_13 | ~spl3_4 | ~spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f127,f91,f79,f130,f83])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    v2_funct_2(sK2,sK0) | ~v3_funct_2(sK2,sK0,sK0) | (~spl3_4 | ~spl3_7)),
% 0.20/0.48    inference(resolution,[],[f126,f80])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v2_funct_2(sK2,X1) | ~v3_funct_2(sK2,X0,X1)) ) | ~spl3_7),
% 0.20/0.48    inference(resolution,[],[f63,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f91])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | v2_funct_2(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ~spl3_9 | spl3_12 | ~spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f121,f91,f123,f104])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(sK2)) | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 | ~v1_relat_1(sK2)) ) | ~spl3_7),
% 0.20/0.48    inference(resolution,[],[f52,f92])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  % (29703)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (29711)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.49  fof(f120,plain,(
% 0.20/0.49    ~spl3_9 | spl3_11 | ~spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f116,f101,f118,f104])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl3_8 <=> sK2 = k7_relat_1(sK2,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    k9_relat_1(sK2,sK0) = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_8),
% 0.20/0.49    inference(superposition,[],[f50,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    sK2 = k7_relat_1(sK2,sK0) | ~spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl3_10),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f113])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    $false | spl3_10),
% 0.20/0.49    inference(resolution,[],[f111,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | spl3_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    spl3_10 <=> v1_relat_1(k2_zfmisc_1(sK0,sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    ~spl3_10 | ~spl3_4 | spl3_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f108,f104,f79,f110])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | (~spl3_4 | spl3_9)),
% 0.20/0.49    inference(resolution,[],[f107,f80])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_9),
% 0.20/0.49    inference(resolution,[],[f105,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f104])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    spl3_8 | ~spl3_9 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f99,f79,f104,f101])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK0) | ~spl3_4),
% 0.20/0.49    inference(resolution,[],[f95,f80])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0) | k7_relat_1(X0,X1) = X0) )),
% 0.20/0.49    inference(resolution,[],[f54,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    spl3_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f91])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    v1_funct_1(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    (sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))) & r1_tarski(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (((k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1 | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1) & r1_tarski(X1,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f15])).
% 0.20/0.49  fof(f15,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_tarski(X1,X0) => (k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1 & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    spl3_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f42,f87])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f43,f83])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    v3_funct_2(sK2,sK0,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f44,f79])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f45,f75])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    r1_tarski(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f46,f71,f68])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) | sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (29701)------------------------------
% 0.20/0.49  % (29701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (29701)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (29701)Memory used [KB]: 10746
% 0.20/0.49  % (29701)Time elapsed: 0.066 s
% 0.20/0.49  % (29701)------------------------------
% 0.20/0.49  % (29701)------------------------------
% 0.20/0.49  % (29694)Success in time 0.131 s
%------------------------------------------------------------------------------
