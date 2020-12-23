%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 150 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :    7
%              Number of atoms          :  251 ( 397 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f67,f71,f75,f81,f93,f98,f104,f110,f115,f122,f127,f131])).

fof(f131,plain,
    ( spl4_1
    | ~ spl4_16
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl4_1
    | ~ spl4_16
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f129,f109])).

fof(f109,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_16
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f129,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | spl4_1
    | ~ spl4_18
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f128,f121])).

fof(f121,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_18
  <=> sK3 = k7_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f128,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | spl4_1
    | ~ spl4_19 ),
    inference(superposition,[],[f36,f126])).

fof(f126,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK1,sK0,sK3,X0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_19
  <=> ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK1,sK0,sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f36,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_1
  <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f127,plain,
    ( spl4_19
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f123,f69,f44,f125])).

fof(f44,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f69,plain,
    ( spl4_9
  <=> ! [X1,X3,X0,X2] :
        ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f123,plain,
    ( ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK1,sK0,sK3,X0)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f70,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f122,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f117,f113,f101,f39,f119])).

fof(f39,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f101,plain,
    ( spl4_15
  <=> sK3 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f113,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f117,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f116,f103])).

fof(f103,plain,
    ( sK3 = k7_relat_1(sK3,sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f101])).

fof(f116,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK1),sK2)
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(resolution,[],[f114,f41])).

fof(f41,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),X1) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,
    ( spl4_17
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f111,f78,f53,f113])).

fof(f53,plain,
    ( spl4_5
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f78,plain,
    ( spl4_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),X1) )
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(resolution,[],[f54,f80])).

fof(f80,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f110,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f105,f73,f44,f107])).

fof(f73,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( r2_relset_1(X0,X1,X2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f105,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f74,f46])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_relset_1(X0,X1,X2,X2) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f104,plain,
    ( spl4_15
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f99,f96,f90,f101])).

fof(f90,plain,
    ( spl4_13
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f96,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | sK3 = k7_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f99,plain,
    ( sK3 = k7_relat_1(sK3,sK1)
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(resolution,[],[f97,f92])).

fof(f92,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | sK3 = k7_relat_1(sK3,X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f94,f78,f49,f96])).

fof(f49,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | sK3 = k7_relat_1(sK3,X0) )
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(resolution,[],[f50,f80])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k7_relat_1(X1,X0) = X1 )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f93,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f88,f65,f44,f90])).

fof(f65,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f88,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(resolution,[],[f66,f46])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f81,plain,
    ( spl4_11
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f76,f57,f44,f78])).

fof(f57,plain,
    ( spl4_6
  <=> ! [X1,X0,X2] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f76,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f75,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(condensation,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f71,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f67,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f59,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f55,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f51,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f49])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f47,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(f42,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f24,f34])).

fof(f24,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.41  % (20465)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (20465)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f132,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f67,f71,f75,f81,f93,f98,f104,f110,f115,f122,f127,f131])).
% 0.22/0.42  fof(f131,plain,(
% 0.22/0.42    spl4_1 | ~spl4_16 | ~spl4_18 | ~spl4_19),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f130])).
% 0.22/0.42  fof(f130,plain,(
% 0.22/0.42    $false | (spl4_1 | ~spl4_16 | ~spl4_18 | ~spl4_19)),
% 0.22/0.42    inference(subsumption_resolution,[],[f129,f109])).
% 0.22/0.42  fof(f109,plain,(
% 0.22/0.42    r2_relset_1(sK1,sK0,sK3,sK3) | ~spl4_16),
% 0.22/0.42    inference(avatar_component_clause,[],[f107])).
% 0.22/0.42  fof(f107,plain,(
% 0.22/0.42    spl4_16 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.42  fof(f129,plain,(
% 0.22/0.42    ~r2_relset_1(sK1,sK0,sK3,sK3) | (spl4_1 | ~spl4_18 | ~spl4_19)),
% 0.22/0.42    inference(forward_demodulation,[],[f128,f121])).
% 0.22/0.42  fof(f121,plain,(
% 0.22/0.42    sK3 = k7_relat_1(sK3,sK2) | ~spl4_18),
% 0.22/0.42    inference(avatar_component_clause,[],[f119])).
% 0.22/0.42  fof(f119,plain,(
% 0.22/0.42    spl4_18 <=> sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.42  fof(f128,plain,(
% 0.22/0.42    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | (spl4_1 | ~spl4_19)),
% 0.22/0.42    inference(superposition,[],[f36,f126])).
% 0.22/0.42  fof(f126,plain,(
% 0.22/0.42    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK1,sK0,sK3,X0)) ) | ~spl4_19),
% 0.22/0.42    inference(avatar_component_clause,[],[f125])).
% 0.22/0.42  fof(f125,plain,(
% 0.22/0.42    spl4_19 <=> ! [X0] : k7_relat_1(sK3,X0) = k5_relset_1(sK1,sK0,sK3,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) | spl4_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f34])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    spl4_1 <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.42  fof(f127,plain,(
% 0.22/0.42    spl4_19 | ~spl4_3 | ~spl4_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f123,f69,f44,f125])).
% 0.22/0.42  fof(f44,plain,(
% 0.22/0.42    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    spl4_9 <=> ! [X1,X3,X0,X2] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.42  fof(f123,plain,(
% 0.22/0.42    ( ! [X0] : (k7_relat_1(sK3,X0) = k5_relset_1(sK1,sK0,sK3,X0)) ) | (~spl4_3 | ~spl4_9)),
% 0.22/0.42    inference(resolution,[],[f70,f46])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f44])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) ) | ~spl4_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f69])).
% 0.22/0.42  fof(f122,plain,(
% 0.22/0.42    spl4_18 | ~spl4_2 | ~spl4_15 | ~spl4_17),
% 0.22/0.42    inference(avatar_split_clause,[],[f117,f113,f101,f39,f119])).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    spl4_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.42  fof(f101,plain,(
% 0.22/0.42    spl4_15 <=> sK3 = k7_relat_1(sK3,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.42  fof(f113,plain,(
% 0.22/0.42    spl4_17 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.42  fof(f117,plain,(
% 0.22/0.42    sK3 = k7_relat_1(sK3,sK2) | (~spl4_2 | ~spl4_15 | ~spl4_17)),
% 0.22/0.42    inference(forward_demodulation,[],[f116,f103])).
% 0.22/0.42  fof(f103,plain,(
% 0.22/0.42    sK3 = k7_relat_1(sK3,sK1) | ~spl4_15),
% 0.22/0.42    inference(avatar_component_clause,[],[f101])).
% 0.22/0.42  fof(f116,plain,(
% 0.22/0.42    k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK1),sK2) | (~spl4_2 | ~spl4_17)),
% 0.22/0.42    inference(resolution,[],[f114,f41])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    r1_tarski(sK1,sK2) | ~spl4_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f39])).
% 0.22/0.42  fof(f114,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),X1)) ) | ~spl4_17),
% 0.22/0.42    inference(avatar_component_clause,[],[f113])).
% 0.22/0.42  fof(f115,plain,(
% 0.22/0.42    spl4_17 | ~spl4_5 | ~spl4_11),
% 0.22/0.42    inference(avatar_split_clause,[],[f111,f78,f53,f113])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl4_5 <=> ! [X1,X0,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.42  fof(f78,plain,(
% 0.22/0.42    spl4_11 <=> v1_relat_1(sK3)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.42  fof(f111,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(sK3,X0) = k7_relat_1(k7_relat_1(sK3,X0),X1)) ) | (~spl4_5 | ~spl4_11)),
% 0.22/0.42    inference(resolution,[],[f54,f80])).
% 0.22/0.42  fof(f80,plain,(
% 0.22/0.42    v1_relat_1(sK3) | ~spl4_11),
% 0.22/0.42    inference(avatar_component_clause,[],[f78])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) ) | ~spl4_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f53])).
% 0.22/0.42  fof(f110,plain,(
% 0.22/0.42    spl4_16 | ~spl4_3 | ~spl4_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f105,f73,f44,f107])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    spl4_10 <=> ! [X1,X0,X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.42  fof(f105,plain,(
% 0.22/0.42    r2_relset_1(sK1,sK0,sK3,sK3) | (~spl4_3 | ~spl4_10)),
% 0.22/0.42    inference(resolution,[],[f74,f46])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) | ~spl4_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f73])).
% 0.22/0.42  fof(f104,plain,(
% 0.22/0.42    spl4_15 | ~spl4_13 | ~spl4_14),
% 0.22/0.42    inference(avatar_split_clause,[],[f99,f96,f90,f101])).
% 0.22/0.42  fof(f90,plain,(
% 0.22/0.42    spl4_13 <=> v4_relat_1(sK3,sK1)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.42  fof(f96,plain,(
% 0.22/0.42    spl4_14 <=> ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.42  fof(f99,plain,(
% 0.22/0.42    sK3 = k7_relat_1(sK3,sK1) | (~spl4_13 | ~spl4_14)),
% 0.22/0.42    inference(resolution,[],[f97,f92])).
% 0.22/0.42  fof(f92,plain,(
% 0.22/0.42    v4_relat_1(sK3,sK1) | ~spl4_13),
% 0.22/0.42    inference(avatar_component_clause,[],[f90])).
% 0.22/0.42  fof(f97,plain,(
% 0.22/0.42    ( ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0)) ) | ~spl4_14),
% 0.22/0.42    inference(avatar_component_clause,[],[f96])).
% 0.22/0.42  fof(f98,plain,(
% 0.22/0.42    spl4_14 | ~spl4_4 | ~spl4_11),
% 0.22/0.42    inference(avatar_split_clause,[],[f94,f78,f49,f96])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    spl4_4 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.42  fof(f94,plain,(
% 0.22/0.42    ( ! [X0] : (~v4_relat_1(sK3,X0) | sK3 = k7_relat_1(sK3,X0)) ) | (~spl4_4 | ~spl4_11)),
% 0.22/0.42    inference(resolution,[],[f50,f80])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) ) | ~spl4_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f49])).
% 0.22/0.42  fof(f93,plain,(
% 0.22/0.42    spl4_13 | ~spl4_3 | ~spl4_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f88,f65,f44,f90])).
% 0.22/0.42  fof(f65,plain,(
% 0.22/0.42    spl4_8 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.42  fof(f88,plain,(
% 0.22/0.42    v4_relat_1(sK3,sK1) | (~spl4_3 | ~spl4_8)),
% 0.22/0.42    inference(resolution,[],[f66,f46])).
% 0.22/0.42  fof(f66,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl4_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f65])).
% 0.22/0.42  fof(f81,plain,(
% 0.22/0.42    spl4_11 | ~spl4_3 | ~spl4_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f76,f57,f44,f78])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    spl4_6 <=> ! [X1,X0,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.42  fof(f76,plain,(
% 0.22/0.42    v1_relat_1(sK3) | (~spl4_3 | ~spl4_6)),
% 0.22/0.42    inference(resolution,[],[f58,f46])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) ) | ~spl4_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f57])).
% 0.22/0.42  fof(f75,plain,(
% 0.22/0.42    spl4_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f32,f73])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.42    inference(condensation,[],[f31])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    inference(flattening,[],[f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    spl4_9),
% 0.22/0.42    inference(avatar_split_clause,[],[f30,f69])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.22/0.42  fof(f67,plain,(
% 0.22/0.42    spl4_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f28,f65])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    spl4_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f27,f57])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl4_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f26,f53])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.42    inference(flattening,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    spl4_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f25,f49])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(flattening,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    spl4_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f22,f44])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.42    inference(cnf_transformation,[],[f21])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.42    inference(flattening,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.22/0.42    inference(negated_conjecture,[],[f7])).
% 0.22/0.42  fof(f7,conjecture,(
% 0.22/0.42    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    spl4_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f23,f39])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    r1_tarski(sK1,sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f21])).
% 0.22/0.42  fof(f37,plain,(
% 0.22/0.42    ~spl4_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f24,f34])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.22/0.42    inference(cnf_transformation,[],[f21])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (20465)------------------------------
% 0.22/0.42  % (20465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (20465)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (20465)Memory used [KB]: 10618
% 0.22/0.42  % (20465)Time elapsed: 0.007 s
% 0.22/0.42  % (20465)------------------------------
% 0.22/0.42  % (20465)------------------------------
% 0.22/0.42  % (20459)Success in time 0.064 s
%------------------------------------------------------------------------------
