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
% DateTime   : Thu Dec  3 13:03:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 188 expanded)
%              Number of leaves         :   19 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  289 ( 529 expanded)
%              Number of equality atoms :   68 ( 138 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f72,f78,f83,f100,f104,f132,f145,f172,f190,f200])).

fof(f200,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f198,f67])).

fof(f67,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_4
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f198,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f197,f70])).

fof(f70,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_5
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f197,plain,
    ( ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f196,f95])).

fof(f95,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f196,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl5_19 ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK3,k2_relat_1(sK2))
    | ~ spl5_19 ),
    inference(superposition,[],[f33,f189])).

fof(f189,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl5_19
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(f190,plain,
    ( spl5_19
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f168,f75,f51,f187])).

fof(f51,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f75,plain,
    ( spl5_6
  <=> k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f168,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3))
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(superposition,[],[f77,f55])).

fof(f55,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl5_3 ),
    inference(resolution,[],[f53,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f77,plain,
    ( k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f75])).

% (26981)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f172,plain,
    ( spl5_5
    | ~ spl5_9
    | ~ spl5_14
    | spl5_15 ),
    inference(avatar_split_clause,[],[f150,f142,f129,f94,f69])).

fof(f129,plain,
    ( spl5_14
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f142,plain,
    ( spl5_15
  <=> r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f150,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_9
    | ~ spl5_14
    | spl5_15 ),
    inference(subsumption_resolution,[],[f148,f137])).

fof(f137,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f135,f95])).

fof(f135,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | ~ spl5_14 ),
    inference(trivial_inequality_removal,[],[f134])).

fof(f134,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | ~ spl5_14 ),
    inference(superposition,[],[f33,f131])).

fof(f131,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f148,plain,
    ( r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | sK1 = k2_relat_1(sK2)
    | spl5_15 ),
    inference(resolution,[],[f144,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f144,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f145,plain,
    ( ~ spl5_15
    | ~ spl5_3
    | spl5_5
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f136,f129,f69,f51,f142])).

fof(f136,plain,
    ( ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1)
    | ~ spl5_3
    | spl5_5
    | ~ spl5_14 ),
    inference(trivial_inequality_removal,[],[f133])).

fof(f133,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1)
    | ~ spl5_3
    | spl5_5
    | ~ spl5_14 ),
    inference(superposition,[],[f73,f131])).

fof(f73,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X3))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl5_3
    | spl5_5 ),
    inference(subsumption_resolution,[],[f61,f71])).

fof(f71,plain,
    ( sK1 != k2_relat_1(sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f61,plain,
    ( ! [X3] :
        ( sK1 = k2_relat_1(sK2)
        | k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X3))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f59,f57])).

fof(f57,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f53,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f59,plain,
    ( ! [X3] :
        ( k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X3))
        | sK1 = k2_relset_1(sK0,sK1,sK2)
        | ~ r2_hidden(X3,sK1) )
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f24,f55])).

fof(f24,plain,(
    ! [X3] :
      ( sK1 = k2_relset_1(sK0,sK1,sK2)
      | ~ r2_hidden(X3,sK1)
      | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X3)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3))
            | ~ r2_hidden(X3,X1) )
      <~> k2_relset_1(X0,X1,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
                & r2_hidden(X3,X1) )
        <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3))
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

fof(f132,plain,
    ( spl5_14
    | spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f127,f98,f94,f69,f129])).

fof(f98,plain,
    ( spl5_10
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(X0,sK1),X0)
        | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(X0,sK1)))
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f127,plain,
    ( k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1)))
    | spl5_5
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f126,f71])).

fof(f126,plain,
    ( sK1 = k2_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1)))
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( sK1 = k2_relat_1(sK2)
    | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1)))
    | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1)))
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(resolution,[],[f106,f95])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | sK1 = k2_relat_1(X0)
        | k1_xboole_0 = k10_relat_1(X0,k1_tarski(sK4(k2_relat_1(X0),sK1)))
        | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(X0),sK1))) )
    | ~ spl5_10 ),
    inference(resolution,[],[f99,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,sK1),X0)
        | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(X0,sK1)))
        | sK1 = X0 )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f104,plain,
    ( ~ spl5_3
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | ~ spl5_3
    | spl5_9 ),
    inference(subsumption_resolution,[],[f102,f30])).

fof(f30,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f102,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_3
    | spl5_9 ),
    inference(resolution,[],[f101,f53])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl5_9 ),
    inference(resolution,[],[f96,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f96,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f100,plain,
    ( ~ spl5_9
    | spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f92,f80,f98,f94])).

fof(f80,plain,
    ( spl5_7
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,sK1),X0)
        | sK1 = X0
        | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(X0,sK1)))
        | ~ v1_relat_1(sK2) )
    | ~ spl5_7 ),
    inference(resolution,[],[f90,f32])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,sK1),k2_relat_1(sK2))
        | ~ r2_hidden(sK4(X0,sK1),X0)
        | sK1 = X0 )
    | ~ spl5_7 ),
    inference(resolution,[],[f84,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f82,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f82,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f83,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f60,f51,f80])).

fof(f60,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f56,f57])).

fof(f56,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(resolution,[],[f53,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f78,plain,
    ( spl5_6
    | ~ spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f63,f51,f69,f75])).

fof(f63,plain,
    ( sK1 != k2_relat_1(sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f23,f57])).

fof(f23,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,
    ( spl5_4
    | ~ spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f62,f51,f69,f65])).

fof(f62,plain,
    ( sK1 != k2_relat_1(sK2)
    | r2_hidden(sK3,sK1)
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f22,f57])).

fof(f22,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f54,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f27,f51])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (26982)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (26956)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (26965)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (26973)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (26973)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f54,f72,f78,f83,f100,f104,f132,f145,f172,f190,f200])).
% 0.21/0.54  fof(f200,plain,(
% 0.21/0.54    ~spl5_4 | ~spl5_5 | ~spl5_9 | ~spl5_19),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f199])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    $false | (~spl5_4 | ~spl5_5 | ~spl5_9 | ~spl5_19)),
% 0.21/0.54    inference(subsumption_resolution,[],[f198,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    r2_hidden(sK3,sK1) | ~spl5_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl5_4 <=> r2_hidden(sK3,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    ~r2_hidden(sK3,sK1) | (~spl5_5 | ~spl5_9 | ~spl5_19)),
% 0.21/0.54    inference(forward_demodulation,[],[f197,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2) | ~spl5_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl5_5 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    ~r2_hidden(sK3,k2_relat_1(sK2)) | (~spl5_9 | ~spl5_19)),
% 0.21/0.54    inference(subsumption_resolution,[],[f196,f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    v1_relat_1(sK2) | ~spl5_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl5_9 <=> v1_relat_1(sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.54  fof(f196,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | ~r2_hidden(sK3,k2_relat_1(sK2)) | ~spl5_19),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | ~r2_hidden(sK3,k2_relat_1(sK2)) | ~spl5_19),
% 0.21/0.54    inference(superposition,[],[f33,f189])).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3)) | ~spl5_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f187])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    spl5_19 <=> k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0 | ~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k10_relat_1(X1,k1_tarski(X0)) != k1_xboole_0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    spl5_19 | ~spl5_3 | ~spl5_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f168,f75,f51,f187])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl5_6 <=> k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK3)) | (~spl5_3 | ~spl5_6)),
% 0.21/0.54    inference(superposition,[],[f77,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0] : (k8_relset_1(sK0,sK1,sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f53,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f51])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) | ~spl5_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f75])).
% 0.21/0.54  % (26981)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    spl5_5 | ~spl5_9 | ~spl5_14 | spl5_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f150,f142,f129,f94,f69])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    spl5_14 <=> k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    spl5_15 <=> r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2) | (~spl5_9 | ~spl5_14 | spl5_15)),
% 0.21/0.54    inference(subsumption_resolution,[],[f148,f137])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ~r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | (~spl5_9 | ~spl5_14)),
% 0.21/0.54    inference(subsumption_resolution,[],[f135,f95])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | ~r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | ~spl5_14),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f134])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | ~r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | ~spl5_14),
% 0.21/0.54    inference(superposition,[],[f33,f131])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1))) | ~spl5_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f129])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    r2_hidden(sK4(k2_relat_1(sK2),sK1),k2_relat_1(sK2)) | sK1 = k2_relat_1(sK2) | spl5_15),
% 0.21/0.54    inference(resolution,[],[f144,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.54  fof(f144,plain,(
% 0.21/0.54    ~r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1) | spl5_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f142])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ~spl5_15 | ~spl5_3 | spl5_5 | ~spl5_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f136,f129,f69,f51,f142])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ~r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1) | (~spl5_3 | spl5_5 | ~spl5_14)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK4(k2_relat_1(sK2),sK1),sK1) | (~spl5_3 | spl5_5 | ~spl5_14)),
% 0.21/0.54    inference(superposition,[],[f73,f131])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X3] : (k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X3)) | ~r2_hidden(X3,sK1)) ) | (~spl5_3 | spl5_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f61,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    sK1 != k2_relat_1(sK2) | spl5_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f69])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X3] : (sK1 = k2_relat_1(sK2) | k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X3)) | ~r2_hidden(X3,sK1)) ) | ~spl5_3),
% 0.21/0.54    inference(backward_demodulation,[],[f59,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f53,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X3] : (k1_xboole_0 != k10_relat_1(sK2,k1_tarski(X3)) | sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1)) ) | ~spl5_3),
% 0.21/0.54    inference(backward_demodulation,[],[f24,f55])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X3] : (sK1 = k2_relset_1(sK0,sK1,sK2) | ~r2_hidden(X3,sK1) | k1_xboole_0 != k8_relset_1(sK0,sK1,sK2,k1_tarski(X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0,X1,X2] : ((! [X3] : (k1_xboole_0 != k8_relset_1(X0,X1,X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) <~> k2_relset_1(X0,X1,X2) = X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(k1_xboole_0 = k8_relset_1(X0,X1,X2,k1_tarski(X3)) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl5_14 | spl5_5 | ~spl5_9 | ~spl5_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f127,f98,f94,f69,f129])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    spl5_10 <=> ! [X0] : (~r2_hidden(sK4(X0,sK1),X0) | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(X0,sK1))) | sK1 = X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1))) | (spl5_5 | ~spl5_9 | ~spl5_10)),
% 0.21/0.54    inference(subsumption_resolution,[],[f126,f71])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1))) | (~spl5_9 | ~spl5_10)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f125])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    sK1 = k2_relat_1(sK2) | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1))) | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(sK2),sK1))) | (~spl5_9 | ~spl5_10)),
% 0.21/0.54    inference(resolution,[],[f106,f95])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | sK1 = k2_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_tarski(sK4(k2_relat_1(X0),sK1))) | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(k2_relat_1(X0),sK1)))) ) | ~spl5_10),
% 0.21/0.54    inference(resolution,[],[f99,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(X1)) | k10_relat_1(X1,k1_tarski(X0)) = k1_xboole_0 | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),X0) | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(X0,sK1))) | sK1 = X0) ) | ~spl5_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f98])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ~spl5_3 | spl5_9),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    $false | (~spl5_3 | spl5_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f102,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl5_3 | spl5_9)),
% 0.21/0.54    inference(resolution,[],[f101,f53])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl5_9),
% 0.21/0.54    inference(resolution,[],[f96,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ~v1_relat_1(sK2) | spl5_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f94])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ~spl5_9 | spl5_10 | ~spl5_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f92,f80,f98,f94])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl5_7 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),X0) | sK1 = X0 | k1_xboole_0 = k10_relat_1(sK2,k1_tarski(sK4(X0,sK1))) | ~v1_relat_1(sK2)) ) | ~spl5_7),
% 0.21/0.54    inference(resolution,[],[f90,f32])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK4(X0,sK1),k2_relat_1(sK2)) | ~r2_hidden(sK4(X0,sK1),X0) | sK1 = X0) ) | ~spl5_7),
% 0.21/0.54    inference(resolution,[],[f84,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl5_7),
% 0.21/0.54    inference(resolution,[],[f82,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl5_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f80])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl5_7 | ~spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f60,f51,f80])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | ~spl5_3),
% 0.21/0.54    inference(backward_demodulation,[],[f56,f57])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) | ~spl5_3),
% 0.21/0.54    inference(resolution,[],[f53,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl5_6 | ~spl5_5 | ~spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f63,f51,f69,f75])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    sK1 != k2_relat_1(sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3)) | ~spl5_3),
% 0.21/0.54    inference(backward_demodulation,[],[f23,f57])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = k8_relset_1(sK0,sK1,sK2,k1_tarski(sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl5_4 | ~spl5_5 | ~spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f62,f51,f69,f65])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    sK1 != k2_relat_1(sK2) | r2_hidden(sK3,sK1) | ~spl5_3),
% 0.21/0.54    inference(backward_demodulation,[],[f22,f57])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    sK1 != k2_relset_1(sK0,sK1,sK2) | r2_hidden(sK3,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f27,f51])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (26973)------------------------------
% 0.21/0.54  % (26973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26973)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (26973)Memory used [KB]: 10874
% 0.21/0.54  % (26973)Time elapsed: 0.114 s
% 0.21/0.54  % (26973)------------------------------
% 0.21/0.54  % (26973)------------------------------
% 0.21/0.54  % (26957)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (26955)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (26951)Success in time 0.175 s
%------------------------------------------------------------------------------
