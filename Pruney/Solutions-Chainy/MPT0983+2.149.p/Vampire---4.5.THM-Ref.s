%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 334 expanded)
%              Number of leaves         :   43 ( 118 expanded)
%              Depth                    :   10
%              Number of atoms          :  540 (1240 expanded)
%              Number of equality atoms :   71 ( 111 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f835,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f120,f129,f133,f139,f403,f405,f407,f415,f466,f481,f488,f525,f549,f575,f579,f606,f608,f612,f661,f664,f680,f754,f834])).

fof(f834,plain,
    ( spl4_2
    | ~ spl4_48 ),
    inference(avatar_contradiction_clause,[],[f833])).

fof(f833,plain,
    ( $false
    | spl4_2
    | ~ spl4_48 ),
    inference(subsumption_resolution,[],[f104,f808])).

fof(f808,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_2
    | ~ spl4_48 ),
    inference(superposition,[],[f100,f679])).

fof(f679,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f677])).

fof(f677,plain,
    ( spl4_48
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f100,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f104,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f83,f82])).

fof(f82,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f51,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f50,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f53,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f754,plain,
    ( ~ spl4_5
    | spl4_1
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f729,f546,f94,f122])).

fof(f122,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f94,plain,
    ( spl4_1
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f546,plain,
    ( spl4_37
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f729,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_37 ),
    inference(superposition,[],[f220,f548])).

fof(f548,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f546])).

fof(f220,plain,(
    ! [X0] :
      ( v2_funct_2(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v2_funct_2(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f87,f177])).

fof(f177,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f87,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f680,plain,
    ( spl4_48
    | ~ spl4_3
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f674,f658,f113,f677])).

fof(f113,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f658,plain,
    ( spl4_47
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f674,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_47 ),
    inference(trivial_inequality_removal,[],[f666])).

fof(f666,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_47 ),
    inference(superposition,[],[f58,f660])).

fof(f660,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f658])).

fof(f58,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f664,plain,
    ( ~ spl4_3
    | ~ spl4_39
    | spl4_46 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_39
    | spl4_46 ),
    inference(unit_resulting_resolution,[],[f115,f618,f656,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f656,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | spl4_46 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl4_46
  <=> r1_tarski(k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f618,plain,
    ( v4_relat_1(sK2,k1_xboole_0)
    | ~ spl4_39 ),
    inference(superposition,[],[f209,f562])).

fof(f562,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl4_39
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f209,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f115,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f661,plain,
    ( ~ spl4_5
    | ~ spl4_3
    | ~ spl4_46
    | spl4_47
    | ~ spl4_28
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f652,f560,f472,f658,f654,f113,f122])).

fof(f472,plain,
    ( spl4_28
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f652,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_28
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f651,f562])).

fof(f651,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_28
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f650,f86])).

fof(f86,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f51])).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f650,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ spl4_28
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f649,f562])).

fof(f649,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f647,f86])).

fof(f647,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ spl4_28 ),
    inference(superposition,[],[f227,f474])).

fof(f474,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f472])).

fof(f227,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2)) ) ),
    inference(resolution,[],[f60,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f612,plain,(
    spl4_42 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | spl4_42 ),
    inference(unit_resulting_resolution,[],[f83,f574])).

fof(f574,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f572])).

fof(f572,plain,
    ( spl4_42
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f608,plain,(
    spl4_41 ),
    inference(avatar_contradiction_clause,[],[f607])).

fof(f607,plain,
    ( $false
    | spl4_41 ),
    inference(subsumption_resolution,[],[f48,f570])).

fof(f570,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_41 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl4_41
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f606,plain,(
    spl4_40 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | spl4_40 ),
    inference(subsumption_resolution,[],[f44,f566])).

fof(f566,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f564])).

fof(f564,plain,
    ( spl4_40
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f44,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f579,plain,(
    spl4_36 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | spl4_36 ),
    inference(subsumption_resolution,[],[f214,f544])).

% (2588)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (2594)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (2583)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (2573)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (2569)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (2576)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (2594)Refutation not found, incomplete strategy% (2594)------------------------------
% (2594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2594)Termination reason: Refutation not found, incomplete strategy

% (2594)Memory used [KB]: 10874
% (2594)Time elapsed: 0.140 s
% (2594)------------------------------
% (2594)------------------------------
% (2584)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (2576)Refutation not found, incomplete strategy% (2576)------------------------------
% (2576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2576)Termination reason: Refutation not found, incomplete strategy

% (2576)Memory used [KB]: 10874
% (2576)Time elapsed: 0.141 s
% (2576)------------------------------
% (2576)------------------------------
% (2586)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (2592)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f544,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl4_36 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl4_36
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f214,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f74,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f575,plain,
    ( spl4_2
    | spl4_39
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_40
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_41
    | ~ spl4_42
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f557,f463,f572,f568,f394,f390,f564,f386,f382,f560,f98])).

fof(f382,plain,
    ( spl4_20
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f386,plain,
    ( spl4_21
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f390,plain,
    ( spl4_22
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f394,plain,
    ( spl4_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f463,plain,
    ( spl4_26
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f557,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f75,f465])).

fof(f465,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f463])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f549,plain,
    ( ~ spl4_36
    | ~ spl4_5
    | spl4_37
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f538,f522,f546,f122,f542])).

fof(f522,plain,
    ( spl4_34
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f538,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl4_34 ),
    inference(resolution,[],[f524,f206])).

fof(f206,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k2_relat_1(X4))
      | k2_relat_1(X4) = X3
      | ~ v1_relat_1(X4)
      | ~ v5_relat_1(X4,X3) ) ),
    inference(resolution,[],[f72,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f524,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f522])).

fof(f525,plain,
    ( ~ spl4_3
    | ~ spl4_5
    | spl4_34
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f520,f472,f522,f122,f113])).

fof(f520,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f499,f85])).

fof(f85,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f57,f51])).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f499,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_28 ),
    inference(superposition,[],[f61,f474])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f488,plain,
    ( ~ spl4_20
    | ~ spl4_21
    | ~ spl4_22
    | ~ spl4_23
    | spl4_28
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f485,f463,f472,f394,f390,f386,f382])).

fof(f485,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_26 ),
    inference(superposition,[],[f79,f465])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f481,plain,(
    spl4_25 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | spl4_25 ),
    inference(unit_resulting_resolution,[],[f47,f43,f45,f49,f461,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f461,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl4_25
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f466,plain,
    ( ~ spl4_25
    | spl4_26 ),
    inference(avatar_split_clause,[],[f455,f463,f459])).

fof(f455,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f307,f46])).

fof(f46,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f307,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f415,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | spl4_23 ),
    inference(subsumption_resolution,[],[f49,f396])).

fof(f396,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f394])).

fof(f407,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl4_22 ),
    inference(subsumption_resolution,[],[f43,f392])).

fof(f392,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f390])).

fof(f405,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f45,f388])).

fof(f388,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f386])).

fof(f403,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | spl4_20 ),
    inference(subsumption_resolution,[],[f47,f384])).

fof(f384,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f382])).

fof(f139,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f63,f128])).

fof(f128,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl4_6
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f133,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f63,f119])).

fof(f119,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f129,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f111,f126,f122])).

fof(f111,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f120,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f110,f117,f113])).

fof(f110,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f49])).

fof(f101,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f42,f98,f94])).

fof(f42,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n015.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 19:12:08 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.45  % (2571)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.46  % (2587)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.47  % (2595)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.47  % (2579)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.48  % (2567)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.49  % (2566)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.49  % (2575)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.49  % (2591)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.19/0.49  % (2568)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.49  % (2577)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.49  % (2570)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.50  % (2572)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (2589)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.51  % (2581)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.51  % (2580)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.51  % (2579)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f835,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f101,f120,f129,f133,f139,f403,f405,f407,f415,f466,f481,f488,f525,f549,f575,f579,f606,f608,f612,f661,f664,f680,f754,f834])).
% 0.19/0.51  fof(f834,plain,(
% 0.19/0.51    spl4_2 | ~spl4_48),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f833])).
% 0.19/0.51  fof(f833,plain,(
% 0.19/0.51    $false | (spl4_2 | ~spl4_48)),
% 0.19/0.51    inference(subsumption_resolution,[],[f104,f808])).
% 0.19/0.51  fof(f808,plain,(
% 0.19/0.51    ~v2_funct_1(k1_xboole_0) | (spl4_2 | ~spl4_48)),
% 0.19/0.51    inference(superposition,[],[f100,f679])).
% 0.19/0.51  fof(f679,plain,(
% 0.19/0.51    k1_xboole_0 = sK2 | ~spl4_48),
% 0.19/0.51    inference(avatar_component_clause,[],[f677])).
% 0.19/0.51  fof(f677,plain,(
% 0.19/0.51    spl4_48 <=> k1_xboole_0 = sK2),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.19/0.51  fof(f100,plain,(
% 0.19/0.51    ~v2_funct_1(sK2) | spl4_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f98])).
% 0.19/0.51  fof(f98,plain,(
% 0.19/0.51    spl4_2 <=> v2_funct_1(sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.51  fof(f104,plain,(
% 0.19/0.51    v2_funct_1(k1_xboole_0)),
% 0.19/0.51    inference(superposition,[],[f83,f82])).
% 0.19/0.51  fof(f82,plain,(
% 0.19/0.51    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.19/0.51    inference(definition_unfolding,[],[f50,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f18])).
% 0.19/0.51  fof(f18,axiom,(
% 0.19/0.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.19/0.51  fof(f50,plain,(
% 0.19/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.51    inference(cnf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,axiom,(
% 0.19/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.19/0.51  fof(f83,plain,(
% 0.19/0.51    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.19/0.51    inference(definition_unfolding,[],[f53,f51])).
% 0.19/0.51  fof(f53,plain,(
% 0.19/0.51    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,axiom,(
% 0.19/0.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.19/0.51  fof(f754,plain,(
% 0.19/0.51    ~spl4_5 | spl4_1 | ~spl4_37),
% 0.19/0.51    inference(avatar_split_clause,[],[f729,f546,f94,f122])).
% 0.19/0.51  fof(f122,plain,(
% 0.19/0.51    spl4_5 <=> v1_relat_1(sK3)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.51  fof(f94,plain,(
% 0.19/0.51    spl4_1 <=> v2_funct_2(sK3,sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.51  fof(f546,plain,(
% 0.19/0.51    spl4_37 <=> sK0 = k2_relat_1(sK3)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.19/0.51  fof(f729,plain,(
% 0.19/0.51    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_37),
% 0.19/0.51    inference(superposition,[],[f220,f548])).
% 0.19/0.51  fof(f548,plain,(
% 0.19/0.51    sK0 = k2_relat_1(sK3) | ~spl4_37),
% 0.19/0.51    inference(avatar_component_clause,[],[f546])).
% 0.19/0.51  fof(f220,plain,(
% 0.19/0.51    ( ! [X0] : (v2_funct_2(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(duplicate_literal_removal,[],[f217])).
% 0.19/0.51  fof(f217,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_relat_1(X0) | v2_funct_2(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(resolution,[],[f87,f177])).
% 0.19/0.51  fof(f177,plain,(
% 0.19/0.51    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(resolution,[],[f66,f88])).
% 0.19/0.51  fof(f88,plain,(
% 0.19/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.51    inference(equality_resolution,[],[f71])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.51  fof(f66,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | v5_relat_1(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.19/0.51  fof(f87,plain,(
% 0.19/0.51    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 0.19/0.51    inference(equality_resolution,[],[f68])).
% 0.19/0.51  fof(f68,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(flattening,[],[f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.51    inference(ennf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,axiom,(
% 0.19/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.19/0.51  fof(f680,plain,(
% 0.19/0.51    spl4_48 | ~spl4_3 | ~spl4_47),
% 0.19/0.51    inference(avatar_split_clause,[],[f674,f658,f113,f677])).
% 0.19/0.51  fof(f113,plain,(
% 0.19/0.51    spl4_3 <=> v1_relat_1(sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.51  fof(f658,plain,(
% 0.19/0.51    spl4_47 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.19/0.51  fof(f674,plain,(
% 0.19/0.51    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl4_47),
% 0.19/0.51    inference(trivial_inequality_removal,[],[f666])).
% 0.19/0.51  fof(f666,plain,(
% 0.19/0.51    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl4_47),
% 0.19/0.51    inference(superposition,[],[f58,f660])).
% 0.19/0.51  fof(f660,plain,(
% 0.19/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_47),
% 0.19/0.51    inference(avatar_component_clause,[],[f658])).
% 0.19/0.51  fof(f58,plain,(
% 0.19/0.51    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(flattening,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.19/0.51  fof(f664,plain,(
% 0.19/0.51    ~spl4_3 | ~spl4_39 | spl4_46),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f662])).
% 0.19/0.51  fof(f662,plain,(
% 0.19/0.51    $false | (~spl4_3 | ~spl4_39 | spl4_46)),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f115,f618,f656,f65])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.51  fof(f656,plain,(
% 0.19/0.51    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | spl4_46),
% 0.19/0.51    inference(avatar_component_clause,[],[f654])).
% 0.19/0.51  fof(f654,plain,(
% 0.19/0.51    spl4_46 <=> r1_tarski(k1_relat_1(sK2),k1_xboole_0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.19/0.51  fof(f618,plain,(
% 0.19/0.51    v4_relat_1(sK2,k1_xboole_0) | ~spl4_39),
% 0.19/0.51    inference(superposition,[],[f209,f562])).
% 0.19/0.51  fof(f562,plain,(
% 0.19/0.51    k1_xboole_0 = sK0 | ~spl4_39),
% 0.19/0.51    inference(avatar_component_clause,[],[f560])).
% 0.19/0.51  fof(f560,plain,(
% 0.19/0.51    spl4_39 <=> k1_xboole_0 = sK0),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.19/0.51  fof(f209,plain,(
% 0.19/0.51    v4_relat_1(sK2,sK0)),
% 0.19/0.51    inference(resolution,[],[f73,f49])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.51    inference(flattening,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.51    inference(ennf_transformation,[],[f21])).
% 0.19/0.51  fof(f21,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.19/0.51    inference(negated_conjecture,[],[f20])).
% 0.19/0.51  fof(f20,conjecture,(
% 0.19/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f33])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.51  fof(f115,plain,(
% 0.19/0.51    v1_relat_1(sK2) | ~spl4_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f113])).
% 0.19/0.51  fof(f661,plain,(
% 0.19/0.51    ~spl4_5 | ~spl4_3 | ~spl4_46 | spl4_47 | ~spl4_28 | ~spl4_39),
% 0.19/0.51    inference(avatar_split_clause,[],[f652,f560,f472,f658,f654,f113,f122])).
% 0.19/0.51  fof(f472,plain,(
% 0.19/0.51    spl4_28 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.19/0.51  fof(f652,plain,(
% 0.19/0.51    k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_28 | ~spl4_39)),
% 0.19/0.51    inference(forward_demodulation,[],[f651,f562])).
% 0.19/0.51  fof(f651,plain,(
% 0.19/0.51    sK0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_28 | ~spl4_39)),
% 0.19/0.51    inference(forward_demodulation,[],[f650,f86])).
% 0.19/0.51  fof(f86,plain,(
% 0.19/0.51    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.19/0.51    inference(definition_unfolding,[],[f56,f51])).
% 0.19/0.51  fof(f56,plain,(
% 0.19/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.19/0.51  fof(f650,plain,(
% 0.19/0.51    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | (~spl4_28 | ~spl4_39)),
% 0.19/0.51    inference(forward_demodulation,[],[f649,f562])).
% 0.19/0.51  fof(f649,plain,(
% 0.19/0.51    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~spl4_28),
% 0.19/0.51    inference(forward_demodulation,[],[f647,f86])).
% 0.19/0.51  fof(f647,plain,(
% 0.19/0.51    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~spl4_28),
% 0.19/0.51    inference(superposition,[],[f227,f474])).
% 0.19/0.51  fof(f474,plain,(
% 0.19/0.51    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_28),
% 0.19/0.51    inference(avatar_component_clause,[],[f472])).
% 0.19/0.51  fof(f227,plain,(
% 0.19/0.51    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2))) )),
% 0.19/0.51    inference(resolution,[],[f60,f72])).
% 0.19/0.51  fof(f72,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f60,plain,(
% 0.19/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f26])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.19/0.51  fof(f612,plain,(
% 0.19/0.51    spl4_42),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f609])).
% 0.19/0.51  fof(f609,plain,(
% 0.19/0.51    $false | spl4_42),
% 0.19/0.51    inference(unit_resulting_resolution,[],[f83,f574])).
% 0.19/0.51  fof(f574,plain,(
% 0.19/0.51    ~v2_funct_1(k6_partfun1(sK0)) | spl4_42),
% 0.19/0.51    inference(avatar_component_clause,[],[f572])).
% 0.19/0.51  fof(f572,plain,(
% 0.19/0.51    spl4_42 <=> v2_funct_1(k6_partfun1(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.19/0.51  fof(f608,plain,(
% 0.19/0.51    spl4_41),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f607])).
% 0.19/0.51  fof(f607,plain,(
% 0.19/0.51    $false | spl4_41),
% 0.19/0.51    inference(subsumption_resolution,[],[f48,f570])).
% 0.19/0.51  fof(f570,plain,(
% 0.19/0.51    ~v1_funct_2(sK2,sK0,sK1) | spl4_41),
% 0.19/0.51    inference(avatar_component_clause,[],[f568])).
% 0.19/0.51  fof(f568,plain,(
% 0.19/0.51    spl4_41 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f606,plain,(
% 0.19/0.51    spl4_40),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f605])).
% 0.19/0.51  fof(f605,plain,(
% 0.19/0.51    $false | spl4_40),
% 0.19/0.51    inference(subsumption_resolution,[],[f44,f566])).
% 0.19/0.51  fof(f566,plain,(
% 0.19/0.51    ~v1_funct_2(sK3,sK1,sK0) | spl4_40),
% 0.19/0.51    inference(avatar_component_clause,[],[f564])).
% 0.19/0.51  fof(f564,plain,(
% 0.19/0.51    spl4_40 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.19/0.51  fof(f44,plain,(
% 0.19/0.51    v1_funct_2(sK3,sK1,sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f23])).
% 0.19/0.51  fof(f579,plain,(
% 0.19/0.51    spl4_36),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f576])).
% 0.19/0.51  fof(f576,plain,(
% 0.19/0.51    $false | spl4_36),
% 0.19/0.51    inference(subsumption_resolution,[],[f214,f544])).
% 0.19/0.51  % (2588)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.51  % (2594)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.51  % (2583)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.19/0.52  % (2573)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.52  % (2569)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.52  % (2576)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.52  % (2594)Refutation not found, incomplete strategy% (2594)------------------------------
% 0.19/0.52  % (2594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (2594)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (2594)Memory used [KB]: 10874
% 0.19/0.52  % (2594)Time elapsed: 0.140 s
% 0.19/0.52  % (2594)------------------------------
% 0.19/0.52  % (2594)------------------------------
% 0.19/0.52  % (2584)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.52  % (2576)Refutation not found, incomplete strategy% (2576)------------------------------
% 0.19/0.52  % (2576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (2576)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (2576)Memory used [KB]: 10874
% 0.19/0.52  % (2576)Time elapsed: 0.141 s
% 0.19/0.52  % (2576)------------------------------
% 0.19/0.52  % (2576)------------------------------
% 0.19/0.52  % (2586)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.52  % (2592)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.52  fof(f544,plain,(
% 0.19/0.52    ~v5_relat_1(sK3,sK0) | spl4_36),
% 0.19/0.52    inference(avatar_component_clause,[],[f542])).
% 0.19/0.52  fof(f542,plain,(
% 0.19/0.52    spl4_36 <=> v5_relat_1(sK3,sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.19/0.52  fof(f214,plain,(
% 0.19/0.52    v5_relat_1(sK3,sK0)),
% 0.19/0.52    inference(resolution,[],[f74,f45])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f74,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f33])).
% 0.19/0.52  fof(f575,plain,(
% 0.19/0.52    spl4_2 | spl4_39 | ~spl4_20 | ~spl4_21 | ~spl4_40 | ~spl4_22 | ~spl4_23 | ~spl4_41 | ~spl4_42 | ~spl4_26),
% 0.19/0.52    inference(avatar_split_clause,[],[f557,f463,f572,f568,f394,f390,f564,f386,f382,f560,f98])).
% 0.19/0.52  fof(f382,plain,(
% 0.19/0.52    spl4_20 <=> v1_funct_1(sK2)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.19/0.52  fof(f386,plain,(
% 0.19/0.52    spl4_21 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.19/0.52  fof(f390,plain,(
% 0.19/0.52    spl4_22 <=> v1_funct_1(sK3)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.19/0.52  fof(f394,plain,(
% 0.19/0.52    spl4_23 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.19/0.52  fof(f463,plain,(
% 0.19/0.52    spl4_26 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.19/0.52  fof(f557,plain,(
% 0.19/0.52    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~spl4_26),
% 0.19/0.52    inference(superposition,[],[f75,f465])).
% 0.19/0.52  fof(f465,plain,(
% 0.19/0.52    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_26),
% 0.19/0.52    inference(avatar_component_clause,[],[f463])).
% 0.19/0.52  fof(f75,plain,(
% 0.19/0.52    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X3)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f35])).
% 0.19/0.52  fof(f35,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.19/0.52    inference(flattening,[],[f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.19/0.52    inference(ennf_transformation,[],[f19])).
% 0.19/0.52  fof(f19,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 0.19/0.52  fof(f549,plain,(
% 0.19/0.52    ~spl4_36 | ~spl4_5 | spl4_37 | ~spl4_34),
% 0.19/0.52    inference(avatar_split_clause,[],[f538,f522,f546,f122,f542])).
% 0.19/0.52  fof(f522,plain,(
% 0.19/0.52    spl4_34 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.19/0.52  fof(f538,plain,(
% 0.19/0.52    sK0 = k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v5_relat_1(sK3,sK0) | ~spl4_34),
% 0.19/0.52    inference(resolution,[],[f524,f206])).
% 0.19/0.52  fof(f206,plain,(
% 0.19/0.52    ( ! [X4,X3] : (~r1_tarski(X3,k2_relat_1(X4)) | k2_relat_1(X4) = X3 | ~v1_relat_1(X4) | ~v5_relat_1(X4,X3)) )),
% 0.19/0.52    inference(resolution,[],[f72,f67])).
% 0.19/0.52  fof(f67,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f30])).
% 0.19/0.52  fof(f524,plain,(
% 0.19/0.52    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl4_34),
% 0.19/0.52    inference(avatar_component_clause,[],[f522])).
% 0.19/0.52  fof(f525,plain,(
% 0.19/0.52    ~spl4_3 | ~spl4_5 | spl4_34 | ~spl4_28),
% 0.19/0.52    inference(avatar_split_clause,[],[f520,f472,f522,f122,f113])).
% 0.19/0.52  fof(f520,plain,(
% 0.19/0.52    r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_28),
% 0.19/0.52    inference(forward_demodulation,[],[f499,f85])).
% 0.19/0.52  fof(f85,plain,(
% 0.19/0.52    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.19/0.52    inference(definition_unfolding,[],[f57,f51])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.19/0.52    inference(cnf_transformation,[],[f9])).
% 0.19/0.52  fof(f499,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_28),
% 0.19/0.52    inference(superposition,[],[f61,f474])).
% 0.19/0.52  fof(f61,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.19/0.52  fof(f488,plain,(
% 0.19/0.52    ~spl4_20 | ~spl4_21 | ~spl4_22 | ~spl4_23 | spl4_28 | ~spl4_26),
% 0.19/0.52    inference(avatar_split_clause,[],[f485,f463,f472,f394,f390,f386,f382])).
% 0.19/0.52  fof(f485,plain,(
% 0.19/0.52    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_26),
% 0.19/0.52    inference(superposition,[],[f79,f465])).
% 0.19/0.52  fof(f79,plain,(
% 0.19/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f39])).
% 0.19/0.52  fof(f39,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.19/0.52    inference(flattening,[],[f38])).
% 0.19/0.52  fof(f38,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.19/0.52    inference(ennf_transformation,[],[f17])).
% 0.19/0.52  fof(f17,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.19/0.52  fof(f481,plain,(
% 0.19/0.52    spl4_25),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f478])).
% 0.19/0.52  fof(f478,plain,(
% 0.19/0.52    $false | spl4_25),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f47,f43,f45,f49,f461,f81])).
% 0.19/0.52  fof(f81,plain,(
% 0.19/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f41])).
% 0.19/0.52  fof(f41,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.19/0.52    inference(flattening,[],[f40])).
% 0.19/0.52  fof(f40,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.19/0.52    inference(ennf_transformation,[],[f15])).
% 0.19/0.52  fof(f15,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.19/0.52  fof(f461,plain,(
% 0.19/0.52    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_25),
% 0.19/0.52    inference(avatar_component_clause,[],[f459])).
% 0.19/0.52  fof(f459,plain,(
% 0.19/0.52    spl4_25 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    v1_funct_1(sK3)),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f47,plain,(
% 0.19/0.52    v1_funct_1(sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f466,plain,(
% 0.19/0.52    ~spl4_25 | spl4_26),
% 0.19/0.52    inference(avatar_split_clause,[],[f455,f463,f459])).
% 0.19/0.52  fof(f455,plain,(
% 0.19/0.52    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.52    inference(resolution,[],[f307,f46])).
% 0.19/0.52  fof(f46,plain,(
% 0.19/0.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  fof(f307,plain,(
% 0.19/0.52    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.19/0.52    inference(resolution,[],[f78,f55])).
% 0.19/0.52  fof(f55,plain,(
% 0.19/0.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,axiom,(
% 0.19/0.52    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.19/0.52  fof(f78,plain,(
% 0.19/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.52    inference(flattening,[],[f36])).
% 0.19/0.52  fof(f36,plain,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.19/0.52    inference(ennf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,axiom,(
% 0.19/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.19/0.52  fof(f415,plain,(
% 0.19/0.52    spl4_23),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f414])).
% 0.19/0.52  fof(f414,plain,(
% 0.19/0.52    $false | spl4_23),
% 0.19/0.52    inference(subsumption_resolution,[],[f49,f396])).
% 0.19/0.52  fof(f396,plain,(
% 0.19/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_23),
% 0.19/0.52    inference(avatar_component_clause,[],[f394])).
% 0.19/0.52  fof(f407,plain,(
% 0.19/0.52    spl4_22),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f406])).
% 0.19/0.52  fof(f406,plain,(
% 0.19/0.52    $false | spl4_22),
% 0.19/0.52    inference(subsumption_resolution,[],[f43,f392])).
% 0.19/0.52  fof(f392,plain,(
% 0.19/0.52    ~v1_funct_1(sK3) | spl4_22),
% 0.19/0.52    inference(avatar_component_clause,[],[f390])).
% 0.19/0.52  fof(f405,plain,(
% 0.19/0.52    spl4_21),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f404])).
% 0.19/0.52  fof(f404,plain,(
% 0.19/0.52    $false | spl4_21),
% 0.19/0.52    inference(subsumption_resolution,[],[f45,f388])).
% 0.19/0.52  fof(f388,plain,(
% 0.19/0.52    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_21),
% 0.19/0.52    inference(avatar_component_clause,[],[f386])).
% 0.19/0.52  fof(f403,plain,(
% 0.19/0.52    spl4_20),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f402])).
% 0.19/0.52  fof(f402,plain,(
% 0.19/0.52    $false | spl4_20),
% 0.19/0.52    inference(subsumption_resolution,[],[f47,f384])).
% 0.19/0.52  fof(f384,plain,(
% 0.19/0.52    ~v1_funct_1(sK2) | spl4_20),
% 0.19/0.52    inference(avatar_component_clause,[],[f382])).
% 0.19/0.52  fof(f139,plain,(
% 0.19/0.52    spl4_6),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f136])).
% 0.19/0.52  fof(f136,plain,(
% 0.19/0.52    $false | spl4_6),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f63,f128])).
% 0.19/0.52  fof(f128,plain,(
% 0.19/0.52    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_6),
% 0.19/0.52    inference(avatar_component_clause,[],[f126])).
% 0.19/0.52  fof(f126,plain,(
% 0.19/0.52    spl4_6 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.52  fof(f133,plain,(
% 0.19/0.52    spl4_4),
% 0.19/0.52    inference(avatar_contradiction_clause,[],[f130])).
% 0.19/0.52  fof(f130,plain,(
% 0.19/0.52    $false | spl4_4),
% 0.19/0.52    inference(unit_resulting_resolution,[],[f63,f119])).
% 0.19/0.52  fof(f119,plain,(
% 0.19/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 0.19/0.52    inference(avatar_component_clause,[],[f117])).
% 0.19/0.52  fof(f117,plain,(
% 0.19/0.52    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.19/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.52  fof(f129,plain,(
% 0.19/0.52    spl4_5 | ~spl4_6),
% 0.19/0.52    inference(avatar_split_clause,[],[f111,f126,f122])).
% 0.19/0.52  fof(f111,plain,(
% 0.19/0.52    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 0.19/0.52    inference(resolution,[],[f62,f45])).
% 0.19/0.52  fof(f62,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.52  fof(f120,plain,(
% 0.19/0.52    spl4_3 | ~spl4_4),
% 0.19/0.52    inference(avatar_split_clause,[],[f110,f117,f113])).
% 0.19/0.52  fof(f110,plain,(
% 0.19/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.19/0.52    inference(resolution,[],[f62,f49])).
% 0.19/0.52  fof(f101,plain,(
% 0.19/0.52    ~spl4_1 | ~spl4_2),
% 0.19/0.52    inference(avatar_split_clause,[],[f42,f98,f94])).
% 0.19/0.52  fof(f42,plain,(
% 0.19/0.52    ~v2_funct_1(sK2) | ~v2_funct_2(sK3,sK0)),
% 0.19/0.52    inference(cnf_transformation,[],[f23])).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (2579)------------------------------
% 0.19/0.52  % (2579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (2579)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (2579)Memory used [KB]: 6652
% 0.19/0.52  % (2579)Time elapsed: 0.151 s
% 0.19/0.52  % (2579)------------------------------
% 0.19/0.52  % (2579)------------------------------
% 0.19/0.52  % (2578)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.52  % (2565)Success in time 0.189 s
%------------------------------------------------------------------------------
