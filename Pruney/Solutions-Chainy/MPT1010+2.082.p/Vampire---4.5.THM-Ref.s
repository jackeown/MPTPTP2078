%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:02 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 247 expanded)
%              Number of leaves         :   24 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  224 ( 494 expanded)
%              Number of equality atoms :   69 ( 207 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f119,f123,f176,f190,f192,f201,f205,f221])).

fof(f221,plain,
    ( ~ spl4_7
    | ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f30,f206])).

fof(f206,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl4_7
    | ~ spl4_17 ),
    inference(superposition,[],[f149,f188])).

fof(f188,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl4_17
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f149,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f146])).

fof(f146,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ spl4_7 ),
    inference(superposition,[],[f31,f114])).

fof(f114,plain,
    ( ! [X0] :
        ( sK1 = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl4_7
  <=> ! [X0] :
        ( sK1 = k1_funct_1(sK3,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f31,plain,(
    sK1 != k1_funct_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f30,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f205,plain,
    ( ~ spl4_13
    | spl4_14
    | spl4_15 ),
    inference(avatar_split_clause,[],[f202,f171,f167,f163])).

fof(f163,plain,
    ( spl4_13
  <=> v1_funct_2(sK3,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f167,plain,
    ( spl4_14
  <=> sK0 = k1_relset_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f171,plain,
    ( spl4_15
  <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f202,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK0 = k1_relset_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3)
    | ~ v1_funct_2(sK3,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f62,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f29,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f59])).

% (4201)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f201,plain,(
    ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f32,f196])).

fof(f196,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_15 ),
    inference(superposition,[],[f67,f173])).

fof(f173,plain,
    ( k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ v1_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : ~ v1_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : ~ v1_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_subset_1)).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f192,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f62,f184])).

fof(f184,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl4_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f190,plain,
    ( ~ spl4_16
    | spl4_17
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f179,f167,f186,f182])).

fof(f179,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | ~ spl4_14 ),
    inference(superposition,[],[f38,f169])).

fof(f169,plain,
    ( sK0 = k1_relset_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f176,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f63,f165])).

fof(f165,plain,
    ( ~ v1_funct_2(sK3,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f63,plain,(
    v1_funct_2(sK3,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f28,f61])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f123,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f27,f111])).

fof(f111,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f75,f107])).

fof(f107,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f75,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f115,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f103,f113,f109,f105])).

fof(f103,plain,(
    ! [X0] :
      ( sK1 = k1_funct_1(sK3,X0)
      | ~ v1_funct_1(sK3)
      | ~ r2_hidden(X0,k1_relat_1(sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f102,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f102,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k4_tarski(X4,X3),sK3)
      | sK1 = X3 ) ),
    inference(resolution,[],[f65,f76])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f62,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:14:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (796622848)
% 0.14/0.38  ipcrm: permission denied for id (796786697)
% 0.14/0.38  ipcrm: permission denied for id (796819467)
% 0.14/0.38  ipcrm: permission denied for id (796852236)
% 0.14/0.38  ipcrm: permission denied for id (796885005)
% 0.14/0.39  ipcrm: permission denied for id (796917775)
% 0.14/0.39  ipcrm: permission denied for id (796950544)
% 0.14/0.39  ipcrm: permission denied for id (797016081)
% 0.14/0.39  ipcrm: permission denied for id (797048850)
% 0.14/0.39  ipcrm: permission denied for id (797147157)
% 0.22/0.40  ipcrm: permission denied for id (797212695)
% 0.22/0.40  ipcrm: permission denied for id (797343770)
% 0.22/0.41  ipcrm: permission denied for id (797474848)
% 0.22/0.42  ipcrm: permission denied for id (797605931)
% 0.22/0.42  ipcrm: permission denied for id (797704238)
% 0.22/0.42  ipcrm: permission denied for id (797769776)
% 0.22/0.43  ipcrm: permission denied for id (797835314)
% 0.22/0.43  ipcrm: permission denied for id (797868085)
% 0.22/0.43  ipcrm: permission denied for id (797966392)
% 0.22/0.44  ipcrm: permission denied for id (797999162)
% 0.22/0.44  ipcrm: permission denied for id (798031932)
% 0.22/0.45  ipcrm: permission denied for id (798163009)
% 0.22/0.45  ipcrm: permission denied for id (798228547)
% 0.22/0.45  ipcrm: permission denied for id (798326854)
% 0.22/0.45  ipcrm: permission denied for id (798425161)
% 0.22/0.46  ipcrm: permission denied for id (798457930)
% 0.22/0.46  ipcrm: permission denied for id (798490699)
% 0.22/0.46  ipcrm: permission denied for id (798556237)
% 0.22/0.46  ipcrm: permission denied for id (798589006)
% 0.22/0.46  ipcrm: permission denied for id (798654545)
% 0.22/0.47  ipcrm: permission denied for id (798720084)
% 0.22/0.47  ipcrm: permission denied for id (798785623)
% 0.22/0.47  ipcrm: permission denied for id (798818392)
% 0.22/0.47  ipcrm: permission denied for id (798851161)
% 0.22/0.48  ipcrm: permission denied for id (798916699)
% 0.22/0.48  ipcrm: permission denied for id (798982238)
% 0.22/0.48  ipcrm: permission denied for id (799047776)
% 0.22/0.49  ipcrm: permission denied for id (799146083)
% 0.22/0.49  ipcrm: permission denied for id (799178852)
% 0.22/0.49  ipcrm: permission denied for id (799211621)
% 0.22/0.49  ipcrm: permission denied for id (799375465)
% 0.22/0.49  ipcrm: permission denied for id (799408234)
% 0.22/0.50  ipcrm: permission denied for id (799441004)
% 0.22/0.51  ipcrm: permission denied for id (799572086)
% 0.22/0.51  ipcrm: permission denied for id (799604855)
% 0.22/0.51  ipcrm: permission denied for id (799637624)
% 0.22/0.51  ipcrm: permission denied for id (799670393)
% 0.35/0.51  ipcrm: permission denied for id (799703163)
% 0.35/0.52  ipcrm: permission denied for id (799768701)
% 0.35/0.52  ipcrm: permission denied for id (799801471)
% 0.38/0.65  % (4186)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.38/0.65  % (4186)Refutation not found, incomplete strategy% (4186)------------------------------
% 0.38/0.65  % (4186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.66  % (4185)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.38/0.66  % (4209)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.38/0.66  % (4186)Termination reason: Refutation not found, incomplete strategy
% 0.38/0.66  
% 0.38/0.66  % (4186)Memory used [KB]: 1791
% 0.38/0.66  % (4186)Time elapsed: 0.087 s
% 0.38/0.66  % (4186)------------------------------
% 0.38/0.66  % (4186)------------------------------
% 0.38/0.66  % (4198)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.38/0.66  % (4193)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.38/0.67  % (4214)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.38/0.67  % (4192)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.38/0.67  % (4198)Refutation found. Thanks to Tanya!
% 0.38/0.67  % SZS status Theorem for theBenchmark
% 0.38/0.67  % SZS output start Proof for theBenchmark
% 0.38/0.67  fof(f222,plain,(
% 0.38/0.67    $false),
% 0.38/0.67    inference(avatar_sat_refutation,[],[f115,f119,f123,f176,f190,f192,f201,f205,f221])).
% 0.38/0.67  fof(f221,plain,(
% 0.38/0.67    ~spl4_7 | ~spl4_17),
% 0.38/0.67    inference(avatar_contradiction_clause,[],[f220])).
% 0.38/0.67  fof(f220,plain,(
% 0.38/0.67    $false | (~spl4_7 | ~spl4_17)),
% 0.38/0.67    inference(subsumption_resolution,[],[f30,f206])).
% 0.38/0.67  fof(f206,plain,(
% 0.38/0.67    ~r2_hidden(sK2,sK0) | (~spl4_7 | ~spl4_17)),
% 0.38/0.67    inference(superposition,[],[f149,f188])).
% 0.38/0.67  fof(f188,plain,(
% 0.38/0.67    sK0 = k1_relat_1(sK3) | ~spl4_17),
% 0.38/0.67    inference(avatar_component_clause,[],[f186])).
% 0.38/0.67  fof(f186,plain,(
% 0.38/0.67    spl4_17 <=> sK0 = k1_relat_1(sK3)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.38/0.67  fof(f149,plain,(
% 0.38/0.67    ~r2_hidden(sK2,k1_relat_1(sK3)) | ~spl4_7),
% 0.38/0.67    inference(trivial_inequality_removal,[],[f146])).
% 0.38/0.67  fof(f146,plain,(
% 0.38/0.67    sK1 != sK1 | ~r2_hidden(sK2,k1_relat_1(sK3)) | ~spl4_7),
% 0.38/0.67    inference(superposition,[],[f31,f114])).
% 0.38/0.67  fof(f114,plain,(
% 0.38/0.67    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl4_7),
% 0.38/0.67    inference(avatar_component_clause,[],[f113])).
% 0.38/0.67  fof(f113,plain,(
% 0.38/0.67    spl4_7 <=> ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~r2_hidden(X0,k1_relat_1(sK3)))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.38/0.67  fof(f31,plain,(
% 0.38/0.67    sK1 != k1_funct_1(sK3,sK2)),
% 0.38/0.67    inference(cnf_transformation,[],[f19])).
% 0.38/0.67  fof(f19,plain,(
% 0.38/0.67    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 0.38/0.67    inference(flattening,[],[f18])).
% 0.38/0.67  fof(f18,plain,(
% 0.38/0.67    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 0.38/0.67    inference(ennf_transformation,[],[f17])).
% 0.38/0.67  fof(f17,negated_conjecture,(
% 0.38/0.67    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.38/0.67    inference(negated_conjecture,[],[f16])).
% 0.38/0.67  fof(f16,conjecture,(
% 0.38/0.67    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 0.38/0.67  fof(f30,plain,(
% 0.38/0.67    r2_hidden(sK2,sK0)),
% 0.38/0.67    inference(cnf_transformation,[],[f19])).
% 0.38/0.67  fof(f205,plain,(
% 0.38/0.67    ~spl4_13 | spl4_14 | spl4_15),
% 0.38/0.67    inference(avatar_split_clause,[],[f202,f171,f167,f163])).
% 0.38/0.67  fof(f163,plain,(
% 0.38/0.67    spl4_13 <=> v1_funct_2(sK3,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.38/0.67  fof(f167,plain,(
% 0.38/0.67    spl4_14 <=> sK0 = k1_relset_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.38/0.67  fof(f171,plain,(
% 0.38/0.67    spl4_15 <=> k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.38/0.67  fof(f202,plain,(
% 0.38/0.67    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | sK0 = k1_relset_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3) | ~v1_funct_2(sK3,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.38/0.67    inference(resolution,[],[f62,f44])).
% 0.38/0.67  fof(f44,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f24])).
% 0.38/0.67  fof(f24,plain,(
% 0.38/0.67    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.67    inference(flattening,[],[f23])).
% 0.38/0.67  fof(f23,plain,(
% 0.38/0.67    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.67    inference(ennf_transformation,[],[f15])).
% 0.38/0.67  fof(f15,axiom,(
% 0.38/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.38/0.67  fof(f62,plain,(
% 0.38/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 0.38/0.67    inference(definition_unfolding,[],[f29,f61])).
% 0.38/0.67  fof(f61,plain,(
% 0.38/0.67    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.38/0.67    inference(definition_unfolding,[],[f33,f60])).
% 0.38/0.67  fof(f60,plain,(
% 0.38/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.38/0.67    inference(definition_unfolding,[],[f34,f59])).
% 0.38/0.67  % (4201)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.38/0.67  fof(f59,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.38/0.67    inference(definition_unfolding,[],[f36,f58])).
% 0.38/0.67  fof(f58,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.38/0.67    inference(definition_unfolding,[],[f48,f57])).
% 0.38/0.67  fof(f57,plain,(
% 0.38/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.38/0.67    inference(definition_unfolding,[],[f52,f56])).
% 0.38/0.67  fof(f56,plain,(
% 0.38/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.38/0.67    inference(definition_unfolding,[],[f54,f55])).
% 0.38/0.67  fof(f55,plain,(
% 0.38/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f8])).
% 0.38/0.67  fof(f8,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.38/0.67  fof(f54,plain,(
% 0.38/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f7])).
% 0.38/0.67  fof(f7,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.38/0.67  fof(f52,plain,(
% 0.38/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f6])).
% 0.38/0.67  fof(f6,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.38/0.67  fof(f48,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f5])).
% 0.38/0.67  fof(f5,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.38/0.67  fof(f36,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f4])).
% 0.38/0.67  fof(f4,axiom,(
% 0.38/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.38/0.67  fof(f34,plain,(
% 0.38/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f3])).
% 0.38/0.67  fof(f3,axiom,(
% 0.38/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.38/0.67  fof(f33,plain,(
% 0.38/0.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f2])).
% 0.38/0.67  fof(f2,axiom,(
% 0.38/0.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.38/0.67  fof(f29,plain,(
% 0.38/0.67    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.38/0.67    inference(cnf_transformation,[],[f19])).
% 0.38/0.67  fof(f201,plain,(
% 0.38/0.67    ~spl4_15),
% 0.38/0.67    inference(avatar_contradiction_clause,[],[f200])).
% 0.38/0.67  fof(f200,plain,(
% 0.38/0.67    $false | ~spl4_15),
% 0.38/0.67    inference(subsumption_resolution,[],[f32,f196])).
% 0.38/0.67  fof(f196,plain,(
% 0.38/0.67    ~v1_xboole_0(k1_xboole_0) | ~spl4_15),
% 0.38/0.67    inference(superposition,[],[f67,f173])).
% 0.38/0.67  fof(f173,plain,(
% 0.38/0.67    k1_xboole_0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl4_15),
% 0.38/0.67    inference(avatar_component_clause,[],[f171])).
% 0.38/0.67  fof(f67,plain,(
% 0.38/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 0.38/0.67    inference(definition_unfolding,[],[f53,f56])).
% 0.38/0.67  fof(f53,plain,(
% 0.38/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f10])).
% 0.38/0.67  fof(f10,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3,X4,X5] : ~v1_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_subset_1)).
% 0.38/0.67  fof(f32,plain,(
% 0.38/0.67    v1_xboole_0(k1_xboole_0)),
% 0.38/0.67    inference(cnf_transformation,[],[f1])).
% 0.38/0.67  fof(f1,axiom,(
% 0.38/0.67    v1_xboole_0(k1_xboole_0)),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.38/0.67  fof(f192,plain,(
% 0.38/0.67    spl4_16),
% 0.38/0.67    inference(avatar_contradiction_clause,[],[f191])).
% 0.38/0.67  fof(f191,plain,(
% 0.38/0.67    $false | spl4_16),
% 0.38/0.67    inference(subsumption_resolution,[],[f62,f184])).
% 0.38/0.67  fof(f184,plain,(
% 0.38/0.67    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | spl4_16),
% 0.38/0.67    inference(avatar_component_clause,[],[f182])).
% 0.38/0.67  fof(f182,plain,(
% 0.38/0.67    spl4_16 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))))),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.38/0.67  fof(f190,plain,(
% 0.38/0.67    ~spl4_16 | spl4_17 | ~spl4_14),
% 0.38/0.67    inference(avatar_split_clause,[],[f179,f167,f186,f182])).
% 0.38/0.67  fof(f179,plain,(
% 0.38/0.67    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | ~spl4_14),
% 0.38/0.67    inference(superposition,[],[f38,f169])).
% 0.38/0.67  fof(f169,plain,(
% 0.38/0.67    sK0 = k1_relset_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK3) | ~spl4_14),
% 0.38/0.67    inference(avatar_component_clause,[],[f167])).
% 0.38/0.67  fof(f38,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f22])).
% 0.38/0.67  fof(f22,plain,(
% 0.38/0.67    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.67    inference(ennf_transformation,[],[f14])).
% 0.38/0.67  fof(f14,axiom,(
% 0.38/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.38/0.67  fof(f176,plain,(
% 0.38/0.67    spl4_13),
% 0.38/0.67    inference(avatar_contradiction_clause,[],[f175])).
% 0.38/0.67  fof(f175,plain,(
% 0.38/0.67    $false | spl4_13),
% 0.38/0.67    inference(subsumption_resolution,[],[f63,f165])).
% 0.38/0.67  fof(f165,plain,(
% 0.38/0.67    ~v1_funct_2(sK3,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | spl4_13),
% 0.38/0.67    inference(avatar_component_clause,[],[f163])).
% 0.38/0.67  fof(f63,plain,(
% 0.38/0.67    v1_funct_2(sK3,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.38/0.67    inference(definition_unfolding,[],[f28,f61])).
% 0.38/0.67  fof(f28,plain,(
% 0.38/0.67    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.38/0.67    inference(cnf_transformation,[],[f19])).
% 0.38/0.67  fof(f123,plain,(
% 0.38/0.67    spl4_6),
% 0.38/0.67    inference(avatar_contradiction_clause,[],[f122])).
% 0.38/0.67  fof(f122,plain,(
% 0.38/0.67    $false | spl4_6),
% 0.38/0.67    inference(subsumption_resolution,[],[f27,f111])).
% 0.38/0.67  fof(f111,plain,(
% 0.38/0.67    ~v1_funct_1(sK3) | spl4_6),
% 0.38/0.67    inference(avatar_component_clause,[],[f109])).
% 0.38/0.67  fof(f109,plain,(
% 0.38/0.67    spl4_6 <=> v1_funct_1(sK3)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.38/0.67  fof(f27,plain,(
% 0.38/0.67    v1_funct_1(sK3)),
% 0.38/0.67    inference(cnf_transformation,[],[f19])).
% 0.38/0.67  fof(f119,plain,(
% 0.38/0.67    spl4_5),
% 0.38/0.67    inference(avatar_contradiction_clause,[],[f116])).
% 0.38/0.67  fof(f116,plain,(
% 0.38/0.67    $false | spl4_5),
% 0.38/0.67    inference(subsumption_resolution,[],[f75,f107])).
% 0.38/0.67  fof(f107,plain,(
% 0.38/0.67    ~v1_relat_1(sK3) | spl4_5),
% 0.38/0.67    inference(avatar_component_clause,[],[f105])).
% 0.38/0.67  fof(f105,plain,(
% 0.38/0.67    spl4_5 <=> v1_relat_1(sK3)),
% 0.38/0.67    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.38/0.67  fof(f75,plain,(
% 0.38/0.67    v1_relat_1(sK3)),
% 0.38/0.67    inference(resolution,[],[f62,f37])).
% 0.38/0.67  fof(f37,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f21])).
% 0.38/0.67  fof(f21,plain,(
% 0.38/0.67    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.38/0.67    inference(ennf_transformation,[],[f13])).
% 0.38/0.67  fof(f13,axiom,(
% 0.38/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.38/0.67  fof(f115,plain,(
% 0.38/0.67    ~spl4_5 | ~spl4_6 | spl4_7),
% 0.38/0.67    inference(avatar_split_clause,[],[f103,f113,f109,f105])).
% 0.38/0.67  fof(f103,plain,(
% 0.38/0.67    ( ! [X0] : (sK1 = k1_funct_1(sK3,X0) | ~v1_funct_1(sK3) | ~r2_hidden(X0,k1_relat_1(sK3)) | ~v1_relat_1(sK3)) )),
% 0.38/0.67    inference(resolution,[],[f102,f73])).
% 0.38/0.67  fof(f73,plain,(
% 0.38/0.67    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.38/0.67    inference(equality_resolution,[],[f47])).
% 0.38/0.67  fof(f47,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f26])).
% 0.38/0.67  fof(f26,plain,(
% 0.38/0.67    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.38/0.67    inference(flattening,[],[f25])).
% 0.38/0.67  fof(f25,plain,(
% 0.38/0.67    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.38/0.67    inference(ennf_transformation,[],[f12])).
% 0.38/0.67  fof(f12,axiom,(
% 0.38/0.67    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.38/0.67  fof(f102,plain,(
% 0.38/0.67    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X4,X3),sK3) | sK1 = X3) )),
% 0.38/0.67    inference(resolution,[],[f65,f76])).
% 0.38/0.67  fof(f76,plain,(
% 0.38/0.67    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) | ~r2_hidden(X0,sK3)) )),
% 0.38/0.67    inference(resolution,[],[f62,f35])).
% 0.38/0.67  fof(f35,plain,(
% 0.38/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.38/0.67    inference(cnf_transformation,[],[f20])).
% 0.38/0.67  fof(f20,plain,(
% 0.38/0.67    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.38/0.67    inference(ennf_transformation,[],[f11])).
% 0.38/0.67  fof(f11,axiom,(
% 0.38/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.38/0.67  fof(f65,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) | X1 = X3) )),
% 0.38/0.67    inference(definition_unfolding,[],[f50,f61])).
% 0.38/0.67  fof(f50,plain,(
% 0.38/0.67    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 0.38/0.67    inference(cnf_transformation,[],[f9])).
% 0.38/0.67  fof(f9,axiom,(
% 0.38/0.67    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.38/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.38/0.67  % SZS output end Proof for theBenchmark
% 0.38/0.67  % (4198)------------------------------
% 0.38/0.67  % (4198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.38/0.67  % (4198)Termination reason: Refutation
% 0.38/0.67  
% 0.38/0.67  % (4198)Memory used [KB]: 6268
% 0.38/0.67  % (4198)Time elapsed: 0.104 s
% 0.38/0.67  % (4198)------------------------------
% 0.38/0.67  % (4198)------------------------------
% 0.38/0.67  % (4051)Success in time 0.311 s
%------------------------------------------------------------------------------
