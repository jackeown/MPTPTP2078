%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 237 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  398 ( 829 expanded)
%              Number of equality atoms :   51 ( 109 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f91,f99,f107,f114,f129,f154,f170,f187,f236,f241,f254,f264,f304,f313])).

fof(f313,plain,
    ( ~ spl3_30
    | spl3_3
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f308,f234,f63,f261])).

fof(f261,plain,
    ( spl3_30
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f63,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f234,plain,
    ( spl3_27
  <=> ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f308,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_3
    | ~ spl3_27 ),
    inference(resolution,[],[f235,f65])).

fof(f65,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f235,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k1_relat_1(sK2),X1) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f234])).

fof(f304,plain,
    ( ~ spl3_30
    | spl3_2
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f300,f239,f59,f261])).

fof(f59,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f239,plain,
    ( spl3_28
  <=> ! [X2] :
        ( ~ r1_tarski(k1_relat_1(sK2),X2)
        | v1_funct_2(k2_funct_1(sK2),sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f300,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_2
    | ~ spl3_28 ),
    inference(resolution,[],[f240,f61])).

fof(f61,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f240,plain,
    ( ! [X2] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X2)
        | ~ r1_tarski(k1_relat_1(sK2),X2) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f239])).

fof(f264,plain,
    ( spl3_30
    | ~ spl3_6
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f257,f248,f78,f261])).

fof(f78,plain,
    ( spl3_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f248,plain,
    ( spl3_29
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f257,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_6
    | ~ spl3_29 ),
    inference(superposition,[],[f204,f250])).

fof(f250,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f248])).

fof(f204,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,X0),sK0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f196,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f196,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f191,f193])).

fof(f193,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f80,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f80,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f191,plain,
    ( ! [X0] : m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f80,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f254,plain,
    ( ~ spl3_11
    | spl3_29
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f253,f180,f151,f95,f88,f73,f248,f111])).

fof(f111,plain,
    ( spl3_11
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f73,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f88,plain,
    ( spl3_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f95,plain,
    ( spl3_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f151,plain,
    ( spl3_17
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f180,plain,
    ( spl3_22
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f253,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f252,f153])).

fof(f153,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f252,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k10_relat_1(sK2,sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f244,f182])).

fof(f182,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f244,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(superposition,[],[f46,f189])).

fof(f189,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f96,f90,f75,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f75,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f90,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f96,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f46,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f241,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | spl3_28
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f237,f180,f151,f239,f55,f111])).

fof(f55,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f237,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(sK2),X2)
        | v1_funct_2(k2_funct_1(sK2),sK1,X2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f224,f153])).

fof(f224,plain,
    ( ! [X2] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X2)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_22 ),
    inference(superposition,[],[f50,f182])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f236,plain,
    ( ~ spl3_11
    | ~ spl3_1
    | spl3_27
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f232,f180,f151,f234,f55,f111])).

fof(f232,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f223,f153])).

fof(f223,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_22 ),
    inference(superposition,[],[f51,f182])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f187,plain,
    ( spl3_22
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f184,f165,f125,f180])).

fof(f125,plain,
    ( spl3_13
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f165,plain,
    ( spl3_19
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f184,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_13
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f127,f167])).

fof(f167,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f165])).

fof(f127,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f170,plain,
    ( spl3_19
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f169,f78,f68,f165])).

fof(f68,plain,
    ( spl3_4
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f169,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f162,f70])).

fof(f70,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f162,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl3_6 ),
    inference(resolution,[],[f45,f80])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f154,plain,
    ( spl3_17
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f149,f95,f88,f73,f151])).

fof(f149,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f96,f90,f75,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f129,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | spl3_13
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f123,f73,f125,f88,f95])).

fof(f123,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f40,f75])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f114,plain,
    ( spl3_11
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f109,f95,f88,f111])).

fof(f109,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f90,f96,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f107,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f106,f78,f95])).

fof(f106,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f53,f80,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f99,plain,
    ( ~ spl3_9
    | ~ spl3_8
    | spl3_1 ),
    inference(avatar_split_clause,[],[f93,f55,f88,f95])).

fof(f93,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f43,f57])).

fof(f57,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f43,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f33,f88])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f81,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f35,f78])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f36,f73])).

fof(f36,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f37,f68])).

fof(f37,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f38,f63,f59,f55])).

fof(f38,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (8146)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.48  % (8146)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f315,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f66,f71,f76,f81,f91,f99,f107,f114,f129,f154,f170,f187,f236,f241,f254,f264,f304,f313])).
% 0.22/0.48  fof(f313,plain,(
% 0.22/0.48    ~spl3_30 | spl3_3 | ~spl3_27),
% 0.22/0.48    inference(avatar_split_clause,[],[f308,f234,f63,f261])).
% 0.22/0.48  fof(f261,plain,(
% 0.22/0.48    spl3_30 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f234,plain,(
% 0.22/0.48    spl3_27 <=> ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.48  fof(f308,plain,(
% 0.22/0.48    ~r1_tarski(k1_relat_1(sK2),sK0) | (spl3_3 | ~spl3_27)),
% 0.22/0.48    inference(resolution,[],[f235,f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f235,plain,(
% 0.22/0.48    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k1_relat_1(sK2),X1)) ) | ~spl3_27),
% 0.22/0.48    inference(avatar_component_clause,[],[f234])).
% 0.22/0.48  fof(f304,plain,(
% 0.22/0.48    ~spl3_30 | spl3_2 | ~spl3_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f300,f239,f59,f261])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f239,plain,(
% 0.22/0.48    spl3_28 <=> ! [X2] : (~r1_tarski(k1_relat_1(sK2),X2) | v1_funct_2(k2_funct_1(sK2),sK1,X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.48  fof(f300,plain,(
% 0.22/0.48    ~r1_tarski(k1_relat_1(sK2),sK0) | (spl3_2 | ~spl3_28)),
% 0.22/0.48    inference(resolution,[],[f240,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f59])).
% 0.22/0.48  fof(f240,plain,(
% 0.22/0.48    ( ! [X2] : (v1_funct_2(k2_funct_1(sK2),sK1,X2) | ~r1_tarski(k1_relat_1(sK2),X2)) ) | ~spl3_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f239])).
% 0.22/0.48  fof(f264,plain,(
% 0.22/0.48    spl3_30 | ~spl3_6 | ~spl3_29),
% 0.22/0.48    inference(avatar_split_clause,[],[f257,f248,f78,f261])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl3_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f248,plain,(
% 0.22/0.48    spl3_29 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.48  fof(f257,plain,(
% 0.22/0.48    r1_tarski(k1_relat_1(sK2),sK0) | (~spl3_6 | ~spl3_29)),
% 0.22/0.48    inference(superposition,[],[f204,f250])).
% 0.22/0.48  fof(f250,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~spl3_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f248])).
% 0.22/0.48  fof(f204,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k10_relat_1(sK2,X0),sK0)) ) | ~spl3_6),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f196,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0))) ) | ~spl3_6),
% 0.22/0.48    inference(backward_demodulation,[],[f191,f193])).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) ) | ~spl3_6),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f80,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f78])).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK0))) ) | ~spl3_6),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f80,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.22/0.48  fof(f254,plain,(
% 0.22/0.48    ~spl3_11 | spl3_29 | ~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_17 | ~spl3_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f253,f180,f151,f95,f88,f73,f248,f111])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    spl3_11 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl3_5 <=> v2_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    spl3_8 <=> v1_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    spl3_9 <=> v1_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    spl3_17 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    spl3_22 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.48  fof(f253,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_17 | ~spl3_22)),
% 0.22/0.48    inference(forward_demodulation,[],[f252,f153])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_17),
% 0.22/0.48    inference(avatar_component_clause,[],[f151])).
% 0.22/0.48  fof(f252,plain,(
% 0.22/0.48    k2_relat_1(k2_funct_1(sK2)) = k10_relat_1(sK2,sK1) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_22)),
% 0.22/0.48    inference(forward_demodulation,[],[f244,f182])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f180])).
% 0.22/0.48  fof(f244,plain,(
% 0.22/0.48    k2_relat_1(k2_funct_1(sK2)) = k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_8 | ~spl3_9)),
% 0.22/0.48    inference(superposition,[],[f46,f189])).
% 0.22/0.48  fof(f189,plain,(
% 0.22/0.48    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)) ) | (~spl3_5 | ~spl3_8 | ~spl3_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f96,f90,f75,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    v2_funct_1(sK2) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f73])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    v1_funct_1(sK2) | ~spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f88])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f95])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.48  fof(f241,plain,(
% 0.22/0.48    ~spl3_11 | ~spl3_1 | spl3_28 | ~spl3_17 | ~spl3_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f237,f180,f151,f239,f55,f111])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f237,plain,(
% 0.22/0.48    ( ! [X2] : (~r1_tarski(k1_relat_1(sK2),X2) | v1_funct_2(k2_funct_1(sK2),sK1,X2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_17 | ~spl3_22)),
% 0.22/0.48    inference(forward_demodulation,[],[f224,f153])).
% 0.22/0.48  fof(f224,plain,(
% 0.22/0.48    ( ! [X2] : (v1_funct_2(k2_funct_1(sK2),sK1,X2) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl3_22),
% 0.22/0.48    inference(superposition,[],[f50,f182])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.48  fof(f236,plain,(
% 0.22/0.48    ~spl3_11 | ~spl3_1 | spl3_27 | ~spl3_17 | ~spl3_22),
% 0.22/0.48    inference(avatar_split_clause,[],[f232,f180,f151,f234,f55,f111])).
% 0.22/0.48  fof(f232,plain,(
% 0.22/0.48    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_17 | ~spl3_22)),
% 0.22/0.48    inference(forward_demodulation,[],[f223,f153])).
% 0.22/0.48  fof(f223,plain,(
% 0.22/0.48    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl3_22),
% 0.22/0.48    inference(superposition,[],[f51,f182])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f29])).
% 0.22/0.48  fof(f187,plain,(
% 0.22/0.48    spl3_22 | ~spl3_13 | ~spl3_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f184,f165,f125,f180])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    spl3_13 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    spl3_19 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl3_13 | ~spl3_19)),
% 0.22/0.48    inference(backward_demodulation,[],[f127,f167])).
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    sK1 = k2_relat_1(sK2) | ~spl3_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f165])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f125])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    spl3_19 | ~spl3_4 | ~spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f169,f78,f68,f165])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_4 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    sK1 = k2_relat_1(sK2) | (~spl3_4 | ~spl3_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f162,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl3_6),
% 0.22/0.48    inference(resolution,[],[f45,f80])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    spl3_17 | ~spl3_5 | ~spl3_8 | ~spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f149,f95,f88,f73,f151])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_8 | ~spl3_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f96,f90,f75,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    ~spl3_9 | ~spl3_8 | spl3_13 | ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f123,f73,f125,f88,f95])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.22/0.48    inference(resolution,[],[f40,f75])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    spl3_11 | ~spl3_8 | ~spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f109,f95,f88,f111])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    v1_relat_1(k2_funct_1(sK2)) | (~spl3_8 | ~spl3_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f90,f96,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    spl3_9 | ~spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f106,f78,f95])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    v1_relat_1(sK2) | ~spl3_6),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f53,f80,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ~spl3_9 | ~spl3_8 | spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f93,f55,f88,f95])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.22/0.48    inference(resolution,[],[f43,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f55])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f88])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v1_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f12])).
% 0.22/0.48  fof(f12,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f78])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f73])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    v2_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f37,f68])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f38,f63,f59,f55])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (8146)------------------------------
% 0.22/0.48  % (8146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8146)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (8146)Memory used [KB]: 10874
% 0.22/0.48  % (8146)Time elapsed: 0.041 s
% 0.22/0.48  % (8146)------------------------------
% 0.22/0.48  % (8146)------------------------------
% 0.22/0.49  % (8139)Success in time 0.125 s
%------------------------------------------------------------------------------
