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
% DateTime   : Thu Dec  3 12:56:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 130 expanded)
%              Number of leaves         :   25 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  206 ( 311 expanded)
%              Number of equality atoms :   17 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f71,f79,f87,f93,f101,f107,f126,f135,f157,f160])).

fof(f160,plain,
    ( sK3 != k7_relat_1(sK3,sK2)
    | r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f157,plain,
    ( ~ spl5_5
    | spl5_16
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f139,f131,f153,f68])).

fof(f68,plain,
    ( spl5_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f153,plain,
    ( spl5_16
  <=> sK3 = k7_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f131,plain,
    ( spl5_13
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f139,plain,
    ( sK3 = k7_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl5_13 ),
    inference(resolution,[],[f133,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f133,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f135,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f129,f116,f49,f131])).

fof(f49,plain,
    ( spl5_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f116,plain,
    ( spl5_11
  <=> sK1 = k2_xboole_0(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f129,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(resolution,[],[f127,f51])).

fof(f51,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_relat_1(sK3),X0) )
    | ~ spl5_11 ),
    inference(superposition,[],[f33,f118])).

fof(f118,plain,
    ( sK1 = k2_xboole_0(k1_relat_1(sK3),sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f126,plain,
    ( spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f114,f83,f116])).

fof(f83,plain,
    ( spl5_7
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f114,plain,
    ( sK1 = k2_xboole_0(k1_relat_1(sK3),sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f85,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f85,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f107,plain,
    ( spl5_10
    | ~ spl5_3
    | spl5_8 ),
    inference(avatar_split_clause,[],[f102,f90,f54,f104])).

fof(f104,plain,
    ( spl5_10
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f54,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f90,plain,
    ( spl5_8
  <=> sP4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f102,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl5_3
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f56,f92,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f41_D])).

fof(f41_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X1,X2,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    <=> ~ sP4(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

% (4346)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f92,plain,
    ( ~ sP4(sK0,sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f56,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f101,plain,
    ( ~ spl5_9
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f96,f54,f44,f98])).

fof(f98,plain,
    ( spl5_9
  <=> r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f44,plain,
    ( spl5_1
  <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f96,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f46,f94])).

fof(f94,plain,
    ( ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f46,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f93,plain,
    ( ~ spl5_8
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f88,f54,f90])).

fof(f88,plain,
    ( ~ sP4(sK0,sK1)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f31,f41_D])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f87,plain,
    ( ~ spl5_5
    | spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f81,f75,f83,f68])).

fof(f75,plain,
    ( spl5_6
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f81,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl5_6 ),
    inference(resolution,[],[f77,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f77,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f79,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f73,f54,f75])).

fof(f73,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f38,f56])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f71,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f66,f54,f68])).

fof(f66,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f40,f56,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f57,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

fof(f52,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f49])).

fof(f29,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f30,f44])).

fof(f30,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:59:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.51  % (4349)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (4349)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f47,f52,f57,f71,f79,f87,f93,f101,f107,f126,f135,f157,f160])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    sK3 != k7_relat_1(sK3,sK2) | r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | ~r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ~spl5_5 | spl5_16 | ~spl5_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f139,f131,f153,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl5_5 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl5_16 <=> sK3 = k7_relat_1(sK3,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl5_13 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    sK3 = k7_relat_1(sK3,sK2) | ~v1_relat_1(sK3) | ~spl5_13),
% 0.21/0.51    inference(resolution,[],[f133,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK3),sK2) | ~spl5_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl5_13 | ~spl5_2 | ~spl5_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f129,f116,f49,f131])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    spl5_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl5_11 <=> sK1 = k2_xboole_0(k1_relat_1(sK3),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK3),sK2) | (~spl5_2 | ~spl5_11)),
% 0.21/0.51    inference(resolution,[],[f127,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f49])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_relat_1(sK3),X0)) ) | ~spl5_11),
% 0.21/0.51    inference(superposition,[],[f33,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(k1_relat_1(sK3),sK1) | ~spl5_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f116])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl5_11 | ~spl5_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f114,f83,f116])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl5_7 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(k1_relat_1(sK3),sK1) | ~spl5_7),
% 0.21/0.51    inference(resolution,[],[f85,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK3),sK1) | ~spl5_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    spl5_10 | ~spl5_3 | spl5_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f102,f90,f54,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl5_10 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl5_8 <=> sP4(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    r2_relset_1(sK1,sK0,sK3,sK3) | (~spl5_3 | spl5_8)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f56,f92,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41_D])).
% 0.21/0.51  fof(f41_D,plain,(
% 0.21/0.51    ( ! [X0,X1] : (( ! [X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) <=> ~sP4(X1,X0)) )),
% 0.21/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.51  % (4346)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~sP4(sK0,sK1) | spl5_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ~spl5_9 | spl5_1 | ~spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f96,f54,f44,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl5_9 <=> r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    spl5_1 <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | (spl5_1 | ~spl5_3)),
% 0.21/0.51    inference(backward_demodulation,[],[f46,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)) ) | ~spl5_3),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f56,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) | spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f44])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~spl5_8 | ~spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f88,f54,f90])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~sP4(sK0,sK1) | ~spl5_3),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f56,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~sP4(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(general_splitting,[],[f31,f41_D])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ~spl5_5 | spl5_7 | ~spl5_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f81,f75,f83,f68])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl5_6 <=> v4_relat_1(sK3,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl5_6),
% 0.21/0.51    inference(resolution,[],[f77,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    v4_relat_1(sK3,sK1) | ~spl5_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    spl5_6 | ~spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f73,f54,f75])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    v4_relat_1(sK3,sK1) | ~spl5_3),
% 0.21/0.51    inference(resolution,[],[f38,f56])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl5_5 | ~spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f66,f54,f68])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl5_3),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f40,f56,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f28,f54])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f49])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ~spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f44])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (4349)------------------------------
% 0.21/0.51  % (4349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4349)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (4349)Memory used [KB]: 10618
% 0.21/0.51  % (4349)Time elapsed: 0.090 s
% 0.21/0.51  % (4349)------------------------------
% 0.21/0.51  % (4349)------------------------------
% 0.21/0.51  % (4342)Success in time 0.143 s
%------------------------------------------------------------------------------
