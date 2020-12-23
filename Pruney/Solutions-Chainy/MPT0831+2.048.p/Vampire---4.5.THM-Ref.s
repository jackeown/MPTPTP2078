%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 158 expanded)
%              Number of leaves         :   27 (  71 expanded)
%              Depth                    :    7
%              Number of atoms          :  269 ( 421 expanded)
%              Number of equality atoms :   31 (  43 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f57,f61,f65,f73,f77,f81,f86,f92,f109,f116,f122,f127,f139,f144,f148])).

fof(f148,plain,
    ( spl4_1
    | ~ spl4_18
    | ~ spl4_21
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_1
    | ~ spl4_18
    | ~ spl4_21
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f146,f121])).

fof(f121,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_18
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f146,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | spl4_1
    | ~ spl4_21
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f145,f138])).

fof(f138,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl4_21
  <=> sK3 = k7_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f145,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | spl4_1
    | ~ spl4_22 ),
    inference(superposition,[],[f38,f143])).

fof(f143,plain,
    ( ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_22
  <=> ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f38,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_1
  <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f144,plain,
    ( spl4_22
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f140,f75,f46,f142])).

fof(f46,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f75,plain,
    ( spl4_10
  <=> ! [X1,X3,X0,X2] :
        ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f140,plain,
    ( ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f76,f48])).

fof(f48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f76,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f139,plain,
    ( spl4_21
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f134,f125,f113,f89,f136])).

fof(f89,plain,
    ( spl4_13
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f113,plain,
    ( spl4_17
  <=> sK3 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f125,plain,
    ( spl4_19
  <=> ! [X0] :
        ( k7_relat_1(X0,sK1) = k7_relat_1(k7_relat_1(X0,sK1),sK2)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f134,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f129,f115])).

fof(f115,plain,
    ( sK3 = k7_relat_1(sK3,sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f129,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK1),sK2)
    | ~ spl4_13
    | ~ spl4_19 ),
    inference(resolution,[],[f126,f91])).

fof(f91,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f89])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,sK1) = k7_relat_1(k7_relat_1(X0,sK1),sK2) )
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f123,f63,f41,f125])).

fof(f41,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f63,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f123,plain,
    ( ! [X0] :
        ( k7_relat_1(X0,sK1) = k7_relat_1(k7_relat_1(X0,sK1),sK2)
        | ~ v1_relat_1(X0) )
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
        | ~ v1_relat_1(X2) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f122,plain,
    ( spl4_18
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f117,f79,f46,f119])).

fof(f79,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( r2_relset_1(X0,X1,X2,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f117,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl4_3
    | ~ spl4_11 ),
    inference(resolution,[],[f80,f48])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_relset_1(X0,X1,X2,X2) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f116,plain,
    ( spl4_17
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f111,f106,f89,f59,f113])).

fof(f59,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = X1
        | ~ v4_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f106,plain,
    ( spl4_16
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f111,plain,
    ( sK3 = k7_relat_1(sK3,sK1)
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f110,f91])).

fof(f110,plain,
    ( sK3 = k7_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(resolution,[],[f60,f108])).

fof(f108,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(X1,X0)
        | k7_relat_1(X1,X0) = X1
        | ~ v1_relat_1(X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f109,plain,
    ( spl4_16
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f104,f71,f46,f106])).

fof(f71,plain,
    ( spl4_9
  <=> ! [X1,X0,X2] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f104,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl4_3
    | ~ spl4_9 ),
    inference(resolution,[],[f72,f48])).

fof(f72,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f92,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f87,f84,f46,f89])).

fof(f84,plain,
    ( spl4_12
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f87,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(resolution,[],[f85,f48])).

fof(f85,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f86,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f82,f55,f51,f84])).

fof(f51,plain,
    ( spl4_4
  <=> ! [X1,X0] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f55,plain,
    ( spl4_5
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | v1_relat_1(X0) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f52,f56])).

fof(f56,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f81,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f34,f79])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(condensation,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f77,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f73,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f65,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f61,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f59])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f57,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f27,f55])).

fof(f27,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f53,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f49,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f36])).

fof(f25,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (14672)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.45  % (14673)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.45  % (14672)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f149,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f57,f61,f65,f73,f77,f81,f86,f92,f109,f116,f122,f127,f139,f144,f148])).
% 0.19/0.45  fof(f148,plain,(
% 0.19/0.45    spl4_1 | ~spl4_18 | ~spl4_21 | ~spl4_22),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f147])).
% 0.19/0.45  fof(f147,plain,(
% 0.19/0.45    $false | (spl4_1 | ~spl4_18 | ~spl4_21 | ~spl4_22)),
% 0.19/0.45    inference(subsumption_resolution,[],[f146,f121])).
% 0.19/0.45  fof(f121,plain,(
% 0.19/0.45    r2_relset_1(sK1,sK0,sK3,sK3) | ~spl4_18),
% 0.19/0.45    inference(avatar_component_clause,[],[f119])).
% 0.19/0.45  fof(f119,plain,(
% 0.19/0.45    spl4_18 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.19/0.45  fof(f146,plain,(
% 0.19/0.45    ~r2_relset_1(sK1,sK0,sK3,sK3) | (spl4_1 | ~spl4_21 | ~spl4_22)),
% 0.19/0.45    inference(forward_demodulation,[],[f145,f138])).
% 0.19/0.45  fof(f138,plain,(
% 0.19/0.45    sK3 = k7_relat_1(sK3,sK2) | ~spl4_21),
% 0.19/0.45    inference(avatar_component_clause,[],[f136])).
% 0.19/0.45  fof(f136,plain,(
% 0.19/0.45    spl4_21 <=> sK3 = k7_relat_1(sK3,sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.19/0.45  fof(f145,plain,(
% 0.19/0.45    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | (spl4_1 | ~spl4_22)),
% 0.19/0.45    inference(superposition,[],[f38,f143])).
% 0.19/0.45  fof(f143,plain,(
% 0.19/0.45    ( ! [X0] : (k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)) ) | ~spl4_22),
% 0.19/0.45    inference(avatar_component_clause,[],[f142])).
% 0.19/0.45  fof(f142,plain,(
% 0.19/0.45    spl4_22 <=> ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) | spl4_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f36])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    spl4_1 <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.45  fof(f144,plain,(
% 0.19/0.45    spl4_22 | ~spl4_3 | ~spl4_10),
% 0.19/0.45    inference(avatar_split_clause,[],[f140,f75,f46,f142])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.45  fof(f75,plain,(
% 0.19/0.45    spl4_10 <=> ! [X1,X3,X0,X2] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.19/0.45  fof(f140,plain,(
% 0.19/0.45    ( ! [X0] : (k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)) ) | (~spl4_3 | ~spl4_10)),
% 0.19/0.45    inference(resolution,[],[f76,f48])).
% 0.19/0.45  fof(f48,plain,(
% 0.19/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f46])).
% 0.19/0.45  fof(f76,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) ) | ~spl4_10),
% 0.19/0.45    inference(avatar_component_clause,[],[f75])).
% 0.19/0.45  fof(f139,plain,(
% 0.19/0.45    spl4_21 | ~spl4_13 | ~spl4_17 | ~spl4_19),
% 0.19/0.45    inference(avatar_split_clause,[],[f134,f125,f113,f89,f136])).
% 0.19/0.45  fof(f89,plain,(
% 0.19/0.45    spl4_13 <=> v1_relat_1(sK3)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.19/0.45  fof(f113,plain,(
% 0.19/0.45    spl4_17 <=> sK3 = k7_relat_1(sK3,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.19/0.45  fof(f125,plain,(
% 0.19/0.45    spl4_19 <=> ! [X0] : (k7_relat_1(X0,sK1) = k7_relat_1(k7_relat_1(X0,sK1),sK2) | ~v1_relat_1(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.19/0.45  fof(f134,plain,(
% 0.19/0.45    sK3 = k7_relat_1(sK3,sK2) | (~spl4_13 | ~spl4_17 | ~spl4_19)),
% 0.19/0.45    inference(forward_demodulation,[],[f129,f115])).
% 0.19/0.45  fof(f115,plain,(
% 0.19/0.45    sK3 = k7_relat_1(sK3,sK1) | ~spl4_17),
% 0.19/0.45    inference(avatar_component_clause,[],[f113])).
% 0.19/0.45  fof(f129,plain,(
% 0.19/0.45    k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK1),sK2) | (~spl4_13 | ~spl4_19)),
% 0.19/0.45    inference(resolution,[],[f126,f91])).
% 0.19/0.45  fof(f91,plain,(
% 0.19/0.45    v1_relat_1(sK3) | ~spl4_13),
% 0.19/0.45    inference(avatar_component_clause,[],[f89])).
% 0.19/0.45  fof(f126,plain,(
% 0.19/0.45    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,sK1) = k7_relat_1(k7_relat_1(X0,sK1),sK2)) ) | ~spl4_19),
% 0.19/0.45    inference(avatar_component_clause,[],[f125])).
% 0.19/0.45  fof(f127,plain,(
% 0.19/0.45    spl4_19 | ~spl4_2 | ~spl4_7),
% 0.19/0.45    inference(avatar_split_clause,[],[f123,f63,f41,f125])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    spl4_2 <=> r1_tarski(sK1,sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.45  fof(f63,plain,(
% 0.19/0.45    spl4_7 <=> ! [X1,X0,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.19/0.45  fof(f123,plain,(
% 0.19/0.45    ( ! [X0] : (k7_relat_1(X0,sK1) = k7_relat_1(k7_relat_1(X0,sK1),sK2) | ~v1_relat_1(X0)) ) | (~spl4_2 | ~spl4_7)),
% 0.19/0.45    inference(resolution,[],[f64,f43])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    r1_tarski(sK1,sK2) | ~spl4_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f41])).
% 0.19/0.45  fof(f64,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) ) | ~spl4_7),
% 0.19/0.45    inference(avatar_component_clause,[],[f63])).
% 0.19/0.45  fof(f122,plain,(
% 0.19/0.45    spl4_18 | ~spl4_3 | ~spl4_11),
% 0.19/0.45    inference(avatar_split_clause,[],[f117,f79,f46,f119])).
% 0.19/0.45  fof(f79,plain,(
% 0.19/0.45    spl4_11 <=> ! [X1,X0,X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.45  fof(f117,plain,(
% 0.19/0.45    r2_relset_1(sK1,sK0,sK3,sK3) | (~spl4_3 | ~spl4_11)),
% 0.19/0.45    inference(resolution,[],[f80,f48])).
% 0.19/0.45  fof(f80,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) | ~spl4_11),
% 0.19/0.45    inference(avatar_component_clause,[],[f79])).
% 0.19/0.45  fof(f116,plain,(
% 0.19/0.45    spl4_17 | ~spl4_6 | ~spl4_13 | ~spl4_16),
% 0.19/0.45    inference(avatar_split_clause,[],[f111,f106,f89,f59,f113])).
% 0.19/0.45  fof(f59,plain,(
% 0.19/0.45    spl4_6 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.45  fof(f106,plain,(
% 0.19/0.45    spl4_16 <=> v4_relat_1(sK3,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.19/0.45  fof(f111,plain,(
% 0.19/0.45    sK3 = k7_relat_1(sK3,sK1) | (~spl4_6 | ~spl4_13 | ~spl4_16)),
% 0.19/0.45    inference(subsumption_resolution,[],[f110,f91])).
% 0.19/0.45  fof(f110,plain,(
% 0.19/0.45    sK3 = k7_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | (~spl4_6 | ~spl4_16)),
% 0.19/0.45    inference(resolution,[],[f60,f108])).
% 0.19/0.45  fof(f108,plain,(
% 0.19/0.45    v4_relat_1(sK3,sK1) | ~spl4_16),
% 0.19/0.45    inference(avatar_component_clause,[],[f106])).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) ) | ~spl4_6),
% 0.19/0.45    inference(avatar_component_clause,[],[f59])).
% 0.19/0.45  fof(f109,plain,(
% 0.19/0.45    spl4_16 | ~spl4_3 | ~spl4_9),
% 0.19/0.45    inference(avatar_split_clause,[],[f104,f71,f46,f106])).
% 0.19/0.45  fof(f71,plain,(
% 0.19/0.45    spl4_9 <=> ! [X1,X0,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.19/0.45  fof(f104,plain,(
% 0.19/0.45    v4_relat_1(sK3,sK1) | (~spl4_3 | ~spl4_9)),
% 0.19/0.45    inference(resolution,[],[f72,f48])).
% 0.19/0.45  fof(f72,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) ) | ~spl4_9),
% 0.19/0.45    inference(avatar_component_clause,[],[f71])).
% 0.19/0.45  fof(f92,plain,(
% 0.19/0.45    spl4_13 | ~spl4_3 | ~spl4_12),
% 0.19/0.45    inference(avatar_split_clause,[],[f87,f84,f46,f89])).
% 0.19/0.45  fof(f84,plain,(
% 0.19/0.45    spl4_12 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.19/0.45  fof(f87,plain,(
% 0.19/0.45    v1_relat_1(sK3) | (~spl4_3 | ~spl4_12)),
% 0.19/0.45    inference(resolution,[],[f85,f48])).
% 0.19/0.45  fof(f85,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | ~spl4_12),
% 0.19/0.45    inference(avatar_component_clause,[],[f84])).
% 0.19/0.45  fof(f86,plain,(
% 0.19/0.45    spl4_12 | ~spl4_4 | ~spl4_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f82,f55,f51,f84])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    spl4_4 <=> ! [X1,X0] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.45  fof(f55,plain,(
% 0.19/0.45    spl4_5 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.45  fof(f82,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) ) | (~spl4_4 | ~spl4_5)),
% 0.19/0.45    inference(resolution,[],[f52,f56])).
% 0.19/0.45  fof(f56,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl4_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f55])).
% 0.19/0.45  fof(f52,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) ) | ~spl4_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f51])).
% 0.19/0.45  fof(f81,plain,(
% 0.19/0.45    spl4_11),
% 0.19/0.45    inference(avatar_split_clause,[],[f34,f79])).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.45    inference(condensation,[],[f33])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    inference(flattening,[],[f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.45    inference(ennf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.19/0.45  fof(f77,plain,(
% 0.19/0.45    spl4_10),
% 0.19/0.45    inference(avatar_split_clause,[],[f32,f75])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.19/0.45  fof(f73,plain,(
% 0.19/0.45    spl4_9),
% 0.19/0.45    inference(avatar_split_clause,[],[f30,f71])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.45    inference(ennf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.45  fof(f65,plain,(
% 0.19/0.45    spl4_7),
% 0.19/0.45    inference(avatar_split_clause,[],[f29,f63])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.19/0.45    inference(flattening,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.19/0.45    inference(ennf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).
% 0.19/0.45  fof(f61,plain,(
% 0.19/0.45    spl4_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f28,f59])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.45    inference(flattening,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.19/0.45  fof(f57,plain,(
% 0.19/0.45    spl4_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f27,f55])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    spl4_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f26,f51])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    spl4_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f23,f46])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f22])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.19/0.46    inference(flattening,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.19/0.46    inference(ennf_transformation,[],[f9])).
% 0.19/0.46  fof(f9,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.19/0.46    inference(negated_conjecture,[],[f8])).
% 0.19/0.46  fof(f8,conjecture,(
% 0.19/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    spl4_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f24,f41])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    r1_tarski(sK1,sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f22])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ~spl4_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f25,f36])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.19/0.46    inference(cnf_transformation,[],[f22])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (14672)------------------------------
% 0.19/0.46  % (14672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (14672)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (14672)Memory used [KB]: 10618
% 0.19/0.46  % (14672)Time elapsed: 0.012 s
% 0.19/0.46  % (14672)------------------------------
% 0.19/0.46  % (14672)------------------------------
% 0.19/0.46  % (14676)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.19/0.46  % (14666)Success in time 0.106 s
%------------------------------------------------------------------------------
