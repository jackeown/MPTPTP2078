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
% DateTime   : Thu Dec  3 13:07:33 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 303 expanded)
%              Number of leaves         :   31 ( 107 expanded)
%              Depth                    :   16
%              Number of atoms          :  476 ( 995 expanded)
%              Number of equality atoms :   70 ( 110 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21275)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f96,f102,f107,f117,f130,f143,f156,f168,f179,f190,f221,f236,f357,f387,f394,f403])).

fof(f403,plain,
    ( ~ spl5_3
    | ~ spl5_7
    | ~ spl5_16
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_16
    | spl5_26 ),
    inference(subsumption_resolution,[],[f401,f86])).

fof(f86,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f401,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl5_7
    | ~ spl5_16
    | spl5_26 ),
    inference(trivial_inequality_removal,[],[f400])).

fof(f400,plain,
    ( sK1 != sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl5_7
    | ~ spl5_16
    | spl5_26 ),
    inference(superposition,[],[f393,f197])).

fof(f197,plain,
    ( ! [X2] :
        ( k1_relat_1(k7_relat_1(sK4,X2)) = X2
        | ~ r1_tarski(X2,sK0) )
    | ~ spl5_7
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f132,f178])).

fof(f178,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl5_16
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f132,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k1_relat_1(sK4))
        | k1_relat_1(k7_relat_1(sK4,X2)) = X2 )
    | ~ spl5_7 ),
    inference(resolution,[],[f116,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f116,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl5_7
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f393,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl5_26
  <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f394,plain,
    ( ~ spl5_26
    | ~ spl5_19
    | spl5_25 ),
    inference(avatar_split_clause,[],[f389,f384,f233,f391])).

fof(f233,plain,
    ( spl5_19
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f384,plain,
    ( spl5_25
  <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f389,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_19
    | spl5_25 ),
    inference(subsumption_resolution,[],[f388,f234])).

fof(f234,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f233])).

fof(f388,plain,
    ( sK1 != k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_25 ),
    inference(superposition,[],[f386,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f386,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f384])).

fof(f387,plain,
    ( ~ spl5_25
    | ~ spl5_1
    | ~ spl5_5
    | spl5_17
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f368,f233,f218,f99,f74,f384])).

fof(f74,plain,
    ( spl5_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f99,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f218,plain,
    ( spl5_17
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f368,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_1
    | ~ spl5_5
    | spl5_17
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f361,f220])).

fof(f220,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f218])).

fof(f361,plain,
    ( sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_19 ),
    inference(resolution,[],[f234,f267])).

fof(f267,plain,
    ( ! [X14,X12,X13] :
        ( ~ m1_subset_1(k7_relat_1(sK4,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | k1_relset_1(X13,X14,k7_relat_1(sK4,X12)) != X13
        | v1_funct_2(k7_relat_1(sK4,X12),X13,X14) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f266,f157])).

fof(f157,plain,
    ( ! [X0] : k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f90,f101])).

fof(f101,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f90,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k2_partfun1(X6,X7,sK4,X8) = k7_relat_1(sK4,X8) )
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f76,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f266,plain,
    ( ! [X14,X12,X13] :
        ( k1_relset_1(X13,X14,k7_relat_1(sK4,X12)) != X13
        | ~ m1_subset_1(k7_relat_1(sK4,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | v1_funct_2(k2_partfun1(sK0,sK3,sK4,X12),X13,X14) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f265,f157])).

fof(f265,plain,
    ( ! [X14,X12,X13] :
        ( ~ m1_subset_1(k7_relat_1(sK4,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | k1_relset_1(X13,X14,k2_partfun1(sK0,sK3,sK4,X12)) != X13
        | v1_funct_2(k2_partfun1(sK0,sK3,sK4,X12),X13,X14) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f155,f157])).

fof(f155,plain,
    ( ! [X14,X12,X13] :
        ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | k1_relset_1(X13,X14,k2_partfun1(sK0,sK3,sK4,X12)) != X13
        | v1_funct_2(k2_partfun1(sK0,sK3,sK4,X12),X13,X14) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f149,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(f149,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f88,f101])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_1(k2_partfun1(X0,X1,sK4,X2)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f357,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | spl5_19 ),
    inference(subsumption_resolution,[],[f355,f116])).

fof(f355,plain,
    ( ~ v1_relat_1(sK4)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_12
    | spl5_19 ),
    inference(subsumption_resolution,[],[f351,f235])).

fof(f235,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f233])).

fof(f351,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_relat_1(sK4)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(resolution,[],[f300,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f300,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),X0)
        | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_12 ),
    inference(resolution,[],[f284,f142])).

fof(f142,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl5_12
  <=> r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f284,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k9_relat_1(sK4,X0),X1)
        | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X2)
        | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) )
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f283,f116])).

fof(f283,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k9_relat_1(sK4,X0),X1)
        | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X2)
        | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_relat_1(sK4) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(superposition,[],[f214,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),X2)
        | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X1)
        | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f211,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f211,plain,
    ( ! [X1] : v1_relat_1(k7_relat_1(sK4,X1))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f209,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f209,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f173,f157])).

fof(f173,plain,
    ( ! [X0] : m1_subset_1(k2_partfun1(sK0,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f89,f101])).

fof(f89,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | m1_subset_1(k2_partfun1(X3,X4,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f236,plain,
    ( ~ spl5_19
    | ~ spl5_1
    | ~ spl5_5
    | spl5_8 ),
    inference(avatar_split_clause,[],[f199,f119,f99,f74,f233])).

fof(f119,plain,
    ( spl5_8
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f199,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_1
    | ~ spl5_5
    | spl5_8 ),
    inference(superposition,[],[f121,f157])).

fof(f121,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f221,plain,
    ( ~ spl5_17
    | ~ spl5_1
    | ~ spl5_5
    | spl5_9 ),
    inference(avatar_split_clause,[],[f200,f123,f99,f74,f218])).

fof(f123,plain,
    ( spl5_9
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f200,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_1
    | ~ spl5_5
    | spl5_9 ),
    inference(superposition,[],[f125,f157])).

fof(f125,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f190,plain,
    ( spl5_2
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl5_2
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f180,f46])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f180,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_15 ),
    inference(superposition,[],[f81,f167])).

fof(f167,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl5_15
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f81,plain,
    ( ~ v1_xboole_0(sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_2
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f179,plain,
    ( spl5_16
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f171,f161,f99,f176])).

fof(f161,plain,
    ( spl5_14
  <=> sK0 = k1_relset_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f171,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f169,f101])).

fof(f169,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_14 ),
    inference(superposition,[],[f163,f56])).

fof(f163,plain,
    ( sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f168,plain,
    ( spl5_14
    | spl5_15
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f159,f99,f93,f165,f161])).

fof(f93,plain,
    ( spl5_4
  <=> v1_funct_2(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f159,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f97,f101])).

fof(f97,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_4 ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f95,plain,
    ( v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f156,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5
    | spl5_10 ),
    inference(resolution,[],[f149,f129])).

fof(f129,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_10
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f143,plain,
    ( spl5_12
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f112,f104,f99,f140])).

fof(f104,plain,
    ( spl5_6
  <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f112,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f111,f101])).

fof(f111,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_6 ),
    inference(superposition,[],[f106,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f106,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f130,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f39,f127,f123,f119])).

fof(f39,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(f117,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f109,f99,f114])).

fof(f109,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(resolution,[],[f101,f55])).

fof(f107,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f44,f104])).

fof(f44,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f102,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f42,f99])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f41,f93])).

fof(f41,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f43,f84])).

fof(f43,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f82,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f40,f74])).

fof(f40,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.07/0.27  % Computer   : n003.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 20:27:27 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.12/0.39  % (21271)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.12/0.39  % (21272)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.12/0.40  % (21278)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.12/0.40  % (21270)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.12/0.41  % (21280)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.12/0.41  % (21279)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.12/0.42  % (21276)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.12/0.42  % (21277)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.42  % (21269)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.12/0.42  % (21282)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.12/0.42  % (21274)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.12/0.42  % (21283)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.12/0.42  % (21266)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.43  % (21285)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.12/0.43  % (21266)Refutation not found, incomplete strategy% (21266)------------------------------
% 0.12/0.43  % (21266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.43  % (21266)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.43  
% 0.12/0.43  % (21266)Memory used [KB]: 10618
% 0.12/0.43  % (21266)Time elapsed: 0.091 s
% 0.12/0.43  % (21266)------------------------------
% 0.12/0.43  % (21266)------------------------------
% 0.12/0.43  % (21267)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.12/0.43  % (21268)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.12/0.43  % (21285)Refutation not found, incomplete strategy% (21285)------------------------------
% 0.12/0.43  % (21285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.43  % (21285)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.43  
% 0.12/0.43  % (21285)Memory used [KB]: 10618
% 0.12/0.43  % (21285)Time elapsed: 0.097 s
% 0.12/0.43  % (21285)------------------------------
% 0.12/0.43  % (21285)------------------------------
% 0.12/0.43  % (21281)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.12/0.43  % (21273)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.12/0.43  % (21265)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.12/0.43  % (21268)Refutation found. Thanks to Tanya!
% 0.12/0.43  % SZS status Theorem for theBenchmark
% 0.12/0.43  % SZS output start Proof for theBenchmark
% 0.12/0.43  % (21275)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.12/0.43  fof(f404,plain,(
% 0.12/0.43    $false),
% 0.12/0.43    inference(avatar_sat_refutation,[],[f77,f82,f87,f96,f102,f107,f117,f130,f143,f156,f168,f179,f190,f221,f236,f357,f387,f394,f403])).
% 0.12/0.43  fof(f403,plain,(
% 0.12/0.43    ~spl5_3 | ~spl5_7 | ~spl5_16 | spl5_26),
% 0.12/0.43    inference(avatar_contradiction_clause,[],[f402])).
% 0.12/0.43  fof(f402,plain,(
% 0.12/0.43    $false | (~spl5_3 | ~spl5_7 | ~spl5_16 | spl5_26)),
% 0.12/0.43    inference(subsumption_resolution,[],[f401,f86])).
% 0.12/0.43  fof(f86,plain,(
% 0.12/0.43    r1_tarski(sK1,sK0) | ~spl5_3),
% 0.12/0.43    inference(avatar_component_clause,[],[f84])).
% 0.12/0.43  fof(f84,plain,(
% 0.12/0.43    spl5_3 <=> r1_tarski(sK1,sK0)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.12/0.43  fof(f401,plain,(
% 0.12/0.43    ~r1_tarski(sK1,sK0) | (~spl5_7 | ~spl5_16 | spl5_26)),
% 0.12/0.43    inference(trivial_inequality_removal,[],[f400])).
% 0.12/0.43  fof(f400,plain,(
% 0.12/0.43    sK1 != sK1 | ~r1_tarski(sK1,sK0) | (~spl5_7 | ~spl5_16 | spl5_26)),
% 0.12/0.43    inference(superposition,[],[f393,f197])).
% 0.12/0.43  fof(f197,plain,(
% 0.12/0.43    ( ! [X2] : (k1_relat_1(k7_relat_1(sK4,X2)) = X2 | ~r1_tarski(X2,sK0)) ) | (~spl5_7 | ~spl5_16)),
% 0.12/0.43    inference(forward_demodulation,[],[f132,f178])).
% 0.12/0.43  fof(f178,plain,(
% 0.12/0.43    sK0 = k1_relat_1(sK4) | ~spl5_16),
% 0.12/0.43    inference(avatar_component_clause,[],[f176])).
% 0.12/0.43  fof(f176,plain,(
% 0.12/0.43    spl5_16 <=> sK0 = k1_relat_1(sK4)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.12/0.43  fof(f132,plain,(
% 0.12/0.43    ( ! [X2] : (~r1_tarski(X2,k1_relat_1(sK4)) | k1_relat_1(k7_relat_1(sK4,X2)) = X2) ) | ~spl5_7),
% 0.12/0.43    inference(resolution,[],[f116,f51])).
% 0.12/0.43  fof(f51,plain,(
% 0.12/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.12/0.43    inference(cnf_transformation,[],[f25])).
% 0.12/0.43  fof(f25,plain,(
% 0.12/0.43    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.12/0.43    inference(flattening,[],[f24])).
% 0.12/0.43  fof(f24,plain,(
% 0.12/0.43    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.12/0.43    inference(ennf_transformation,[],[f7])).
% 0.12/0.43  fof(f7,axiom,(
% 0.12/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 0.12/0.43  fof(f116,plain,(
% 0.12/0.43    v1_relat_1(sK4) | ~spl5_7),
% 0.12/0.43    inference(avatar_component_clause,[],[f114])).
% 0.12/0.43  fof(f114,plain,(
% 0.12/0.43    spl5_7 <=> v1_relat_1(sK4)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.12/0.43  fof(f393,plain,(
% 0.12/0.43    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | spl5_26),
% 0.12/0.43    inference(avatar_component_clause,[],[f391])).
% 0.12/0.43  fof(f391,plain,(
% 0.12/0.43    spl5_26 <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.12/0.43  fof(f394,plain,(
% 0.12/0.43    ~spl5_26 | ~spl5_19 | spl5_25),
% 0.12/0.43    inference(avatar_split_clause,[],[f389,f384,f233,f391])).
% 0.12/0.43  fof(f233,plain,(
% 0.12/0.43    spl5_19 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.12/0.43  fof(f384,plain,(
% 0.12/0.43    spl5_25 <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.12/0.43  fof(f389,plain,(
% 0.12/0.43    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_19 | spl5_25)),
% 0.12/0.43    inference(subsumption_resolution,[],[f388,f234])).
% 0.12/0.43  fof(f234,plain,(
% 0.12/0.43    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_19),
% 0.12/0.43    inference(avatar_component_clause,[],[f233])).
% 0.12/0.43  fof(f388,plain,(
% 0.12/0.43    sK1 != k1_relat_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_25),
% 0.12/0.43    inference(superposition,[],[f386,f56])).
% 0.12/0.43  fof(f56,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f29])).
% 0.12/0.43  fof(f29,plain,(
% 0.12/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.43    inference(ennf_transformation,[],[f9])).
% 0.12/0.43  fof(f9,axiom,(
% 0.12/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.12/0.43  fof(f386,plain,(
% 0.12/0.43    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | spl5_25),
% 0.12/0.43    inference(avatar_component_clause,[],[f384])).
% 0.12/0.43  fof(f387,plain,(
% 0.12/0.43    ~spl5_25 | ~spl5_1 | ~spl5_5 | spl5_17 | ~spl5_19),
% 0.12/0.43    inference(avatar_split_clause,[],[f368,f233,f218,f99,f74,f384])).
% 0.12/0.43  fof(f74,plain,(
% 0.12/0.43    spl5_1 <=> v1_funct_1(sK4)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.12/0.43  fof(f99,plain,(
% 0.12/0.43    spl5_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.12/0.43  fof(f218,plain,(
% 0.12/0.43    spl5_17 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.12/0.43  fof(f368,plain,(
% 0.12/0.43    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl5_1 | ~spl5_5 | spl5_17 | ~spl5_19)),
% 0.12/0.43    inference(subsumption_resolution,[],[f361,f220])).
% 0.12/0.43  fof(f220,plain,(
% 0.12/0.43    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_17),
% 0.12/0.43    inference(avatar_component_clause,[],[f218])).
% 0.12/0.43  fof(f361,plain,(
% 0.12/0.43    sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_1 | ~spl5_5 | ~spl5_19)),
% 0.12/0.43    inference(resolution,[],[f234,f267])).
% 0.12/0.43  fof(f267,plain,(
% 0.12/0.43    ( ! [X14,X12,X13] : (~m1_subset_1(k7_relat_1(sK4,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | k1_relset_1(X13,X14,k7_relat_1(sK4,X12)) != X13 | v1_funct_2(k7_relat_1(sK4,X12),X13,X14)) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(forward_demodulation,[],[f266,f157])).
% 0.12/0.43  fof(f157,plain,(
% 0.12/0.43    ( ! [X0] : (k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(resolution,[],[f90,f101])).
% 0.12/0.43  fof(f101,plain,(
% 0.12/0.43    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_5),
% 0.12/0.43    inference(avatar_component_clause,[],[f99])).
% 0.12/0.43  fof(f90,plain,(
% 0.12/0.43    ( ! [X6,X8,X7] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k2_partfun1(X6,X7,sK4,X8) = k7_relat_1(sK4,X8)) ) | ~spl5_1),
% 0.12/0.43    inference(resolution,[],[f76,f65])).
% 0.12/0.43  fof(f65,plain,(
% 0.12/0.43    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.12/0.43    inference(cnf_transformation,[],[f36])).
% 0.12/0.43  fof(f36,plain,(
% 0.12/0.43    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.12/0.43    inference(flattening,[],[f35])).
% 0.12/0.43  fof(f35,plain,(
% 0.12/0.43    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.12/0.43    inference(ennf_transformation,[],[f14])).
% 0.12/0.43  fof(f14,axiom,(
% 0.12/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.12/0.43  fof(f76,plain,(
% 0.12/0.43    v1_funct_1(sK4) | ~spl5_1),
% 0.12/0.43    inference(avatar_component_clause,[],[f74])).
% 0.12/0.43  fof(f266,plain,(
% 0.12/0.43    ( ! [X14,X12,X13] : (k1_relset_1(X13,X14,k7_relat_1(sK4,X12)) != X13 | ~m1_subset_1(k7_relat_1(sK4,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | v1_funct_2(k2_partfun1(sK0,sK3,sK4,X12),X13,X14)) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(forward_demodulation,[],[f265,f157])).
% 0.12/0.43  fof(f265,plain,(
% 0.12/0.43    ( ! [X14,X12,X13] : (~m1_subset_1(k7_relat_1(sK4,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | k1_relset_1(X13,X14,k2_partfun1(sK0,sK3,sK4,X12)) != X13 | v1_funct_2(k2_partfun1(sK0,sK3,sK4,X12),X13,X14)) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(forward_demodulation,[],[f155,f157])).
% 0.12/0.43  fof(f155,plain,(
% 0.12/0.43    ( ! [X14,X12,X13] : (~m1_subset_1(k2_partfun1(sK0,sK3,sK4,X12),k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | k1_relset_1(X13,X14,k2_partfun1(sK0,sK3,sK4,X12)) != X13 | v1_funct_2(k2_partfun1(sK0,sK3,sK4,X12),X13,X14)) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(resolution,[],[f149,f63])).
% 0.12/0.43  fof(f63,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.12/0.43    inference(cnf_transformation,[],[f33])).
% 0.12/0.43  fof(f33,plain,(
% 0.12/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.12/0.43    inference(flattening,[],[f32])).
% 0.12/0.43  fof(f32,plain,(
% 0.12/0.43    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.12/0.43    inference(ennf_transformation,[],[f15])).
% 0.12/0.43  fof(f15,axiom,(
% 0.12/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).
% 0.12/0.43  fof(f149,plain,(
% 0.12/0.43    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(resolution,[],[f88,f101])).
% 0.12/0.43  fof(f88,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))) ) | ~spl5_1),
% 0.12/0.43    inference(resolution,[],[f76,f66])).
% 0.12/0.43  fof(f66,plain,(
% 0.12/0.43    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f38])).
% 0.12/0.43  fof(f38,plain,(
% 0.12/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.12/0.43    inference(flattening,[],[f37])).
% 0.12/0.43  fof(f37,plain,(
% 0.12/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.12/0.43    inference(ennf_transformation,[],[f13])).
% 0.12/0.43  fof(f13,axiom,(
% 0.12/0.43    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.12/0.43  fof(f357,plain,(
% 0.12/0.43    ~spl5_1 | ~spl5_5 | ~spl5_7 | ~spl5_12 | spl5_19),
% 0.12/0.43    inference(avatar_contradiction_clause,[],[f356])).
% 0.12/0.43  fof(f356,plain,(
% 0.12/0.43    $false | (~spl5_1 | ~spl5_5 | ~spl5_7 | ~spl5_12 | spl5_19)),
% 0.12/0.43    inference(subsumption_resolution,[],[f355,f116])).
% 0.12/0.43  fof(f355,plain,(
% 0.12/0.43    ~v1_relat_1(sK4) | (~spl5_1 | ~spl5_5 | ~spl5_7 | ~spl5_12 | spl5_19)),
% 0.12/0.43    inference(subsumption_resolution,[],[f351,f235])).
% 0.12/0.43  fof(f235,plain,(
% 0.12/0.43    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_19),
% 0.12/0.43    inference(avatar_component_clause,[],[f233])).
% 0.12/0.43  fof(f351,plain,(
% 0.12/0.43    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_relat_1(sK4) | (~spl5_1 | ~spl5_5 | ~spl5_7 | ~spl5_12)),
% 0.12/0.43    inference(resolution,[],[f300,f49])).
% 0.12/0.43  fof(f49,plain,(
% 0.12/0.43    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.12/0.43    inference(cnf_transformation,[],[f22])).
% 0.12/0.43  fof(f22,plain,(
% 0.12/0.43    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.12/0.43    inference(ennf_transformation,[],[f5])).
% 0.12/0.43  fof(f5,axiom,(
% 0.12/0.43    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.12/0.43  fof(f300,plain,(
% 0.12/0.43    ( ! [X0] : (~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),X0) | m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | (~spl5_1 | ~spl5_5 | ~spl5_7 | ~spl5_12)),
% 0.12/0.43    inference(resolution,[],[f284,f142])).
% 0.12/0.43  fof(f142,plain,(
% 0.12/0.43    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~spl5_12),
% 0.12/0.43    inference(avatar_component_clause,[],[f140])).
% 0.12/0.43  fof(f140,plain,(
% 0.12/0.43    spl5_12 <=> r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.12/0.43  fof(f284,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(sK4,X0),X1) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X2) | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) ) | (~spl5_1 | ~spl5_5 | ~spl5_7)),
% 0.12/0.43    inference(subsumption_resolution,[],[f283,f116])).
% 0.12/0.43  fof(f283,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k9_relat_1(sK4,X0),X1) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X2) | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_relat_1(sK4)) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(superposition,[],[f214,f50])).
% 0.12/0.43  fof(f50,plain,(
% 0.12/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.12/0.43    inference(cnf_transformation,[],[f23])).
% 0.12/0.43  fof(f23,plain,(
% 0.12/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.12/0.43    inference(ennf_transformation,[],[f4])).
% 0.12/0.43  fof(f4,axiom,(
% 0.12/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.12/0.43  fof(f214,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),X2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X1) | m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(resolution,[],[f211,f54])).
% 0.12/0.43  fof(f54,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f27])).
% 0.12/0.43  fof(f27,plain,(
% 0.12/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.12/0.43    inference(flattening,[],[f26])).
% 0.12/0.43  fof(f26,plain,(
% 0.12/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.12/0.43    inference(ennf_transformation,[],[f11])).
% 0.12/0.43  fof(f11,axiom,(
% 0.12/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.12/0.43  fof(f211,plain,(
% 0.12/0.43    ( ! [X1] : (v1_relat_1(k7_relat_1(sK4,X1))) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(resolution,[],[f209,f55])).
% 0.12/0.43  fof(f55,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.12/0.43    inference(cnf_transformation,[],[f28])).
% 0.12/0.43  fof(f28,plain,(
% 0.12/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.43    inference(ennf_transformation,[],[f8])).
% 0.12/0.43  fof(f8,axiom,(
% 0.12/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.12/0.43  fof(f209,plain,(
% 0.12/0.43    ( ! [X0] : (m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(forward_demodulation,[],[f173,f157])).
% 0.12/0.43  fof(f173,plain,(
% 0.12/0.43    ( ! [X0] : (m1_subset_1(k2_partfun1(sK0,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))) ) | (~spl5_1 | ~spl5_5)),
% 0.12/0.43    inference(resolution,[],[f89,f101])).
% 0.12/0.43  fof(f89,plain,(
% 0.12/0.43    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | m1_subset_1(k2_partfun1(X3,X4,sK4,X5),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl5_1),
% 0.12/0.43    inference(resolution,[],[f76,f67])).
% 0.12/0.43  fof(f67,plain,(
% 0.12/0.43    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f38])).
% 0.12/0.43  fof(f236,plain,(
% 0.12/0.43    ~spl5_19 | ~spl5_1 | ~spl5_5 | spl5_8),
% 0.12/0.43    inference(avatar_split_clause,[],[f199,f119,f99,f74,f233])).
% 0.12/0.43  fof(f119,plain,(
% 0.12/0.43    spl5_8 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.12/0.43  fof(f199,plain,(
% 0.12/0.43    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_1 | ~spl5_5 | spl5_8)),
% 0.12/0.43    inference(superposition,[],[f121,f157])).
% 0.12/0.43  fof(f121,plain,(
% 0.12/0.43    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_8),
% 0.12/0.43    inference(avatar_component_clause,[],[f119])).
% 0.12/0.43  fof(f221,plain,(
% 0.12/0.43    ~spl5_17 | ~spl5_1 | ~spl5_5 | spl5_9),
% 0.12/0.43    inference(avatar_split_clause,[],[f200,f123,f99,f74,f218])).
% 0.12/0.43  fof(f123,plain,(
% 0.12/0.43    spl5_9 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.12/0.43  fof(f200,plain,(
% 0.12/0.43    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_1 | ~spl5_5 | spl5_9)),
% 0.12/0.43    inference(superposition,[],[f125,f157])).
% 0.12/0.43  fof(f125,plain,(
% 0.12/0.43    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_9),
% 0.12/0.43    inference(avatar_component_clause,[],[f123])).
% 0.12/0.43  fof(f190,plain,(
% 0.12/0.43    spl5_2 | ~spl5_15),
% 0.12/0.43    inference(avatar_contradiction_clause,[],[f189])).
% 0.12/0.43  fof(f189,plain,(
% 0.12/0.43    $false | (spl5_2 | ~spl5_15)),
% 0.12/0.43    inference(subsumption_resolution,[],[f180,f46])).
% 0.12/0.43  fof(f46,plain,(
% 0.12/0.43    v1_xboole_0(k1_xboole_0)),
% 0.12/0.43    inference(cnf_transformation,[],[f1])).
% 0.12/0.44  fof(f1,axiom,(
% 0.12/0.44    v1_xboole_0(k1_xboole_0)),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.12/0.44  fof(f180,plain,(
% 0.12/0.44    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_15)),
% 0.12/0.44    inference(superposition,[],[f81,f167])).
% 0.12/0.44  fof(f167,plain,(
% 0.12/0.44    k1_xboole_0 = sK3 | ~spl5_15),
% 0.12/0.44    inference(avatar_component_clause,[],[f165])).
% 0.12/0.44  fof(f165,plain,(
% 0.12/0.44    spl5_15 <=> k1_xboole_0 = sK3),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.12/0.44  fof(f81,plain,(
% 0.12/0.44    ~v1_xboole_0(sK3) | spl5_2),
% 0.12/0.44    inference(avatar_component_clause,[],[f79])).
% 0.12/0.44  fof(f79,plain,(
% 0.12/0.44    spl5_2 <=> v1_xboole_0(sK3)),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.12/0.44  fof(f179,plain,(
% 0.12/0.44    spl5_16 | ~spl5_5 | ~spl5_14),
% 0.12/0.44    inference(avatar_split_clause,[],[f171,f161,f99,f176])).
% 0.12/0.44  fof(f161,plain,(
% 0.12/0.44    spl5_14 <=> sK0 = k1_relset_1(sK0,sK3,sK4)),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.12/0.44  fof(f171,plain,(
% 0.12/0.44    sK0 = k1_relat_1(sK4) | (~spl5_5 | ~spl5_14)),
% 0.12/0.44    inference(subsumption_resolution,[],[f169,f101])).
% 0.12/0.44  fof(f169,plain,(
% 0.12/0.44    sK0 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_14),
% 0.12/0.44    inference(superposition,[],[f163,f56])).
% 0.12/0.44  fof(f163,plain,(
% 0.12/0.44    sK0 = k1_relset_1(sK0,sK3,sK4) | ~spl5_14),
% 0.12/0.44    inference(avatar_component_clause,[],[f161])).
% 0.12/0.44  fof(f168,plain,(
% 0.12/0.44    spl5_14 | spl5_15 | ~spl5_4 | ~spl5_5),
% 0.12/0.44    inference(avatar_split_clause,[],[f159,f99,f93,f165,f161])).
% 0.12/0.44  fof(f93,plain,(
% 0.12/0.44    spl5_4 <=> v1_funct_2(sK4,sK0,sK3)),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.12/0.44  fof(f159,plain,(
% 0.12/0.44    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | (~spl5_4 | ~spl5_5)),
% 0.12/0.44    inference(subsumption_resolution,[],[f97,f101])).
% 0.12/0.44  fof(f97,plain,(
% 0.12/0.44    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_4),
% 0.12/0.44    inference(resolution,[],[f95,f62])).
% 0.12/0.44  fof(f62,plain,(
% 0.12/0.44    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.44    inference(cnf_transformation,[],[f31])).
% 0.12/0.44  fof(f31,plain,(
% 0.12/0.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.44    inference(flattening,[],[f30])).
% 0.12/0.44  fof(f30,plain,(
% 0.12/0.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.44    inference(ennf_transformation,[],[f12])).
% 0.12/0.44  fof(f12,axiom,(
% 0.12/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.12/0.44  fof(f95,plain,(
% 0.12/0.44    v1_funct_2(sK4,sK0,sK3) | ~spl5_4),
% 0.12/0.44    inference(avatar_component_clause,[],[f93])).
% 0.12/0.44  fof(f156,plain,(
% 0.12/0.44    ~spl5_1 | ~spl5_5 | spl5_10),
% 0.12/0.44    inference(avatar_contradiction_clause,[],[f151])).
% 0.12/0.44  fof(f151,plain,(
% 0.12/0.44    $false | (~spl5_1 | ~spl5_5 | spl5_10)),
% 0.12/0.44    inference(resolution,[],[f149,f129])).
% 0.12/0.44  fof(f129,plain,(
% 0.12/0.44    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_10),
% 0.12/0.44    inference(avatar_component_clause,[],[f127])).
% 0.12/0.44  fof(f127,plain,(
% 0.12/0.44    spl5_10 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.12/0.44  fof(f143,plain,(
% 0.12/0.44    spl5_12 | ~spl5_5 | ~spl5_6),
% 0.12/0.44    inference(avatar_split_clause,[],[f112,f104,f99,f140])).
% 0.12/0.44  fof(f104,plain,(
% 0.12/0.44    spl5_6 <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.12/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.12/0.44  fof(f112,plain,(
% 0.12/0.44    r1_tarski(k9_relat_1(sK4,sK1),sK2) | (~spl5_5 | ~spl5_6)),
% 0.12/0.44    inference(subsumption_resolution,[],[f111,f101])).
% 0.12/0.44  fof(f111,plain,(
% 0.12/0.44    r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_6),
% 0.12/0.44    inference(superposition,[],[f106,f64])).
% 0.12/0.44  fof(f64,plain,(
% 0.12/0.44    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.44    inference(cnf_transformation,[],[f34])).
% 0.12/0.44  fof(f34,plain,(
% 0.12/0.44    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.44    inference(ennf_transformation,[],[f10])).
% 0.12/0.44  fof(f10,axiom,(
% 0.12/0.44    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.12/0.44  fof(f106,plain,(
% 0.12/0.44    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) | ~spl5_6),
% 0.12/0.44    inference(avatar_component_clause,[],[f104])).
% 0.12/0.44  fof(f130,plain,(
% 0.12/0.44    ~spl5_8 | ~spl5_9 | ~spl5_10),
% 0.12/0.44    inference(avatar_split_clause,[],[f39,f127,f123,f119])).
% 0.12/0.44  fof(f39,plain,(
% 0.12/0.44    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.12/0.44    inference(cnf_transformation,[],[f19])).
% 0.12/0.44  fof(f19,plain,(
% 0.12/0.44    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 0.12/0.44    inference(flattening,[],[f18])).
% 0.12/0.44  fof(f18,plain,(
% 0.12/0.44    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 0.12/0.44    inference(ennf_transformation,[],[f17])).
% 0.12/0.44  fof(f17,negated_conjecture,(
% 0.12/0.44    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.12/0.44    inference(negated_conjecture,[],[f16])).
% 0.12/0.44  fof(f16,conjecture,(
% 0.12/0.44    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 0.12/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 0.12/0.44  fof(f117,plain,(
% 0.12/0.44    spl5_7 | ~spl5_5),
% 0.12/0.44    inference(avatar_split_clause,[],[f109,f99,f114])).
% 0.12/0.44  fof(f109,plain,(
% 0.12/0.44    v1_relat_1(sK4) | ~spl5_5),
% 0.12/0.44    inference(resolution,[],[f101,f55])).
% 0.12/0.44  fof(f107,plain,(
% 0.12/0.44    spl5_6),
% 0.12/0.44    inference(avatar_split_clause,[],[f44,f104])).
% 0.12/0.44  fof(f44,plain,(
% 0.12/0.44    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 0.12/0.44    inference(cnf_transformation,[],[f19])).
% 0.12/0.44  fof(f102,plain,(
% 0.12/0.44    spl5_5),
% 0.12/0.44    inference(avatar_split_clause,[],[f42,f99])).
% 0.12/0.44  fof(f42,plain,(
% 0.12/0.44    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.12/0.44    inference(cnf_transformation,[],[f19])).
% 0.12/0.44  fof(f96,plain,(
% 0.12/0.44    spl5_4),
% 0.12/0.44    inference(avatar_split_clause,[],[f41,f93])).
% 0.12/0.44  fof(f41,plain,(
% 0.12/0.44    v1_funct_2(sK4,sK0,sK3)),
% 0.12/0.44    inference(cnf_transformation,[],[f19])).
% 0.12/0.44  fof(f87,plain,(
% 0.12/0.44    spl5_3),
% 0.12/0.44    inference(avatar_split_clause,[],[f43,f84])).
% 0.12/0.44  fof(f43,plain,(
% 0.12/0.44    r1_tarski(sK1,sK0)),
% 0.12/0.44    inference(cnf_transformation,[],[f19])).
% 0.12/0.44  fof(f82,plain,(
% 0.12/0.44    ~spl5_2),
% 0.12/0.44    inference(avatar_split_clause,[],[f45,f79])).
% 0.12/0.44  fof(f45,plain,(
% 0.12/0.44    ~v1_xboole_0(sK3)),
% 0.12/0.44    inference(cnf_transformation,[],[f19])).
% 0.12/0.44  fof(f77,plain,(
% 0.12/0.44    spl5_1),
% 0.12/0.44    inference(avatar_split_clause,[],[f40,f74])).
% 0.12/0.44  fof(f40,plain,(
% 0.12/0.44    v1_funct_1(sK4)),
% 0.12/0.44    inference(cnf_transformation,[],[f19])).
% 0.12/0.44  % SZS output end Proof for theBenchmark
% 0.12/0.44  % (21268)------------------------------
% 0.12/0.44  % (21268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.44  % (21268)Termination reason: Refutation
% 0.12/0.44  
% 0.12/0.44  % (21268)Memory used [KB]: 10874
% 0.12/0.44  % (21268)Time elapsed: 0.098 s
% 0.12/0.44  % (21268)------------------------------
% 0.12/0.44  % (21268)------------------------------
% 0.12/0.44  % (21264)Success in time 0.162 s
%------------------------------------------------------------------------------
