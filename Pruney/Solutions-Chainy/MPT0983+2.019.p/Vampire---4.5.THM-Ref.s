%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:35 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 259 expanded)
%              Number of leaves         :   37 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  435 (1130 expanded)
%              Number of equality atoms :   43 (  50 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f113,f140,f164,f174,f181,f243,f268,f298,f301,f303,f313,f369,f371,f373,f377,f384,f397,f410,f414,f452])).

fof(f452,plain,
    ( spl4_6
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | spl4_6
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f47,f438])).

fof(f438,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_6
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f425,f75])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f425,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | spl4_6
    | ~ spl4_29 ),
    inference(superposition,[],[f112,f356])).

fof(f356,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl4_29
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f112,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_6
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f414,plain,(
    spl4_37 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | spl4_37 ),
    inference(subsumption_resolution,[],[f197,f409])).

fof(f409,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl4_37
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f197,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f64,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f410,plain,
    ( spl4_1
    | ~ spl4_9
    | ~ spl4_37
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f400,f393,f407,f133,f80])).

fof(f80,plain,
    ( spl4_1
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f133,plain,
    ( spl4_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f393,plain,
    ( spl4_35
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f400,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | v2_funct_2(sK3,sK0)
    | ~ spl4_35 ),
    inference(superposition,[],[f73,f395])).

fof(f395,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f393])).

fof(f73,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f397,plain,
    ( ~ spl4_21
    | spl4_35
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f391,f381,f393,f279])).

fof(f279,plain,
    ( spl4_21
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f381,plain,
    ( spl4_33
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f391,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_33 ),
    inference(superposition,[],[f62,f383])).

fof(f383,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f381])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f384,plain,
    ( spl4_33
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_31
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f378,f358,f279,f275,f362,f287,f283,f381])).

fof(f283,plain,
    ( spl4_22
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f287,plain,
    ( spl4_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f362,plain,
    ( spl4_31
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f275,plain,
    ( spl4_20
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f358,plain,
    ( spl4_30
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f378,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f65,f43])).

fof(f43,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

% (32370)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (32357)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (32372)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (32378)Refutation not found, incomplete strategy% (32378)------------------------------
% (32378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f377,plain,(
    spl4_32 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl4_32 ),
    inference(unit_resulting_resolution,[],[f72,f368])).

fof(f368,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_32 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl4_32
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f72,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f48,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f373,plain,(
    spl4_31 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl4_31 ),
    inference(subsumption_resolution,[],[f45,f364])).

fof(f364,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_31 ),
    inference(avatar_component_clause,[],[f362])).

fof(f45,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f371,plain,(
    spl4_30 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl4_30 ),
    inference(subsumption_resolution,[],[f41,f360])).

fof(f360,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f358])).

fof(f41,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f369,plain,
    ( spl4_2
    | spl4_29
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_30
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_31
    | ~ spl4_32
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f352,f240,f366,f362,f287,f283,f358,f279,f275,f354,f84])).

fof(f84,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f240,plain,
    ( spl4_19
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f352,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl4_19 ),
    inference(superposition,[],[f66,f242])).

fof(f242,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f240])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f313,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl4_23 ),
    inference(subsumption_resolution,[],[f46,f289])).

fof(f289,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f287])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f303,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl4_22 ),
    inference(subsumption_resolution,[],[f40,f285])).

fof(f285,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f283])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f301,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f42,f281])).

fof(f281,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f279])).

fof(f298,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl4_20 ),
    inference(subsumption_resolution,[],[f44,f277])).

fof(f277,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f275])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f268,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl4_18 ),
    inference(unit_resulting_resolution,[],[f44,f40,f42,f46,f238,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f238,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl4_18
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f243,plain,
    ( ~ spl4_18
    | spl4_19 ),
    inference(avatar_split_clause,[],[f234,f240,f236])).

fof(f234,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f225,f43])).

fof(f225,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f181,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl4_11 ),
    inference(unit_resulting_resolution,[],[f56,f46,f143,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f143,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f174,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f167,f142,f106,f84])).

fof(f106,plain,
    ( spl4_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f167,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f55,f44])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f164,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f56,f139])).

fof(f139,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_10
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f140,plain,
    ( spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f128,f137,f133])).

fof(f128,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f54,f42])).

fof(f113,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f94,f110,f106])).

fof(f94,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f53,f46])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f87,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f39,f84,f80])).

fof(f39,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:53:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.56  % (32356)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (32368)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (32360)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (32376)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (32378)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.52/0.58  % (32369)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.52/0.58  % (32358)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.52/0.58  % (32359)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.52/0.58  % (32355)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.52/0.59  % (32364)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.52/0.59  % (32361)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.59  % (32368)Refutation found. Thanks to Tanya!
% 1.52/0.59  % SZS status Theorem for theBenchmark
% 1.52/0.59  % (32380)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.52/0.60  % (32375)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.52/0.60  % SZS output start Proof for theBenchmark
% 1.52/0.60  fof(f453,plain,(
% 1.52/0.60    $false),
% 1.52/0.60    inference(avatar_sat_refutation,[],[f87,f113,f140,f164,f174,f181,f243,f268,f298,f301,f303,f313,f369,f371,f373,f377,f384,f397,f410,f414,f452])).
% 1.52/0.60  fof(f452,plain,(
% 1.52/0.60    spl4_6 | ~spl4_29),
% 1.52/0.60    inference(avatar_contradiction_clause,[],[f451])).
% 1.52/0.60  fof(f451,plain,(
% 1.52/0.60    $false | (spl4_6 | ~spl4_29)),
% 1.52/0.60    inference(subsumption_resolution,[],[f47,f438])).
% 1.52/0.60  fof(f438,plain,(
% 1.52/0.60    ~v1_xboole_0(k1_xboole_0) | (spl4_6 | ~spl4_29)),
% 1.52/0.60    inference(forward_demodulation,[],[f425,f75])).
% 1.52/0.60  fof(f75,plain,(
% 1.52/0.60    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.52/0.60    inference(equality_resolution,[],[f60])).
% 1.52/0.60  fof(f60,plain,(
% 1.52/0.60    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f2])).
% 1.52/0.60  fof(f2,axiom,(
% 1.52/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.52/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.52/0.60  fof(f425,plain,(
% 1.52/0.60    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | (spl4_6 | ~spl4_29)),
% 1.52/0.60    inference(superposition,[],[f112,f356])).
% 1.52/0.60  fof(f356,plain,(
% 1.52/0.60    k1_xboole_0 = sK0 | ~spl4_29),
% 1.52/0.60    inference(avatar_component_clause,[],[f354])).
% 1.52/0.60  fof(f354,plain,(
% 1.52/0.60    spl4_29 <=> k1_xboole_0 = sK0),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.52/0.60  fof(f112,plain,(
% 1.52/0.60    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_6),
% 1.52/0.60    inference(avatar_component_clause,[],[f110])).
% 1.52/0.60  fof(f110,plain,(
% 1.52/0.60    spl4_6 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.52/0.60  fof(f47,plain,(
% 1.52/0.60    v1_xboole_0(k1_xboole_0)),
% 1.52/0.60    inference(cnf_transformation,[],[f1])).
% 1.52/0.60  fof(f1,axiom,(
% 1.52/0.60    v1_xboole_0(k1_xboole_0)),
% 1.52/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.52/0.60  fof(f414,plain,(
% 1.52/0.60    spl4_37),
% 1.52/0.60    inference(avatar_contradiction_clause,[],[f411])).
% 1.52/0.60  fof(f411,plain,(
% 1.52/0.60    $false | spl4_37),
% 1.52/0.60    inference(subsumption_resolution,[],[f197,f409])).
% 1.52/0.60  fof(f409,plain,(
% 1.52/0.60    ~v5_relat_1(sK3,sK0) | spl4_37),
% 1.52/0.60    inference(avatar_component_clause,[],[f407])).
% 1.52/0.60  fof(f407,plain,(
% 1.52/0.60    spl4_37 <=> v5_relat_1(sK3,sK0)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.52/0.60  fof(f197,plain,(
% 1.52/0.60    v5_relat_1(sK3,sK0)),
% 1.52/0.60    inference(resolution,[],[f64,f42])).
% 1.52/0.60  fof(f42,plain,(
% 1.52/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.52/0.60    inference(cnf_transformation,[],[f21])).
% 1.52/0.60  fof(f21,plain,(
% 1.52/0.60    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.52/0.60    inference(flattening,[],[f20])).
% 1.52/0.60  fof(f20,plain,(
% 1.52/0.60    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.52/0.60    inference(ennf_transformation,[],[f19])).
% 1.52/0.60  fof(f19,negated_conjecture,(
% 1.52/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.52/0.60    inference(negated_conjecture,[],[f18])).
% 1.52/0.60  fof(f18,conjecture,(
% 1.52/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.52/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.52/0.60  fof(f64,plain,(
% 1.52/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f30])).
% 1.52/0.60  fof(f30,plain,(
% 1.52/0.60    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.60    inference(ennf_transformation,[],[f9])).
% 1.52/0.60  fof(f9,axiom,(
% 1.52/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.52/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.52/0.60  fof(f410,plain,(
% 1.52/0.60    spl4_1 | ~spl4_9 | ~spl4_37 | ~spl4_35),
% 1.52/0.60    inference(avatar_split_clause,[],[f400,f393,f407,f133,f80])).
% 1.52/0.60  fof(f80,plain,(
% 1.52/0.60    spl4_1 <=> v2_funct_2(sK3,sK0)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.52/0.60  fof(f133,plain,(
% 1.52/0.60    spl4_9 <=> v1_relat_1(sK3)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.52/0.60  fof(f393,plain,(
% 1.52/0.60    spl4_35 <=> sK0 = k2_relat_1(sK3)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.52/0.60  fof(f400,plain,(
% 1.52/0.60    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | v2_funct_2(sK3,sK0) | ~spl4_35),
% 1.52/0.60    inference(superposition,[],[f73,f395])).
% 1.52/0.60  fof(f395,plain,(
% 1.52/0.60    sK0 = k2_relat_1(sK3) | ~spl4_35),
% 1.52/0.60    inference(avatar_component_clause,[],[f393])).
% 1.52/0.60  fof(f73,plain,(
% 1.52/0.60    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 1.52/0.60    inference(equality_resolution,[],[f57])).
% 1.52/0.60  fof(f57,plain,(
% 1.52/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 1.52/0.60    inference(cnf_transformation,[],[f28])).
% 1.52/0.60  fof(f28,plain,(
% 1.52/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.52/0.60    inference(flattening,[],[f27])).
% 1.52/0.60  fof(f27,plain,(
% 1.52/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.52/0.60    inference(ennf_transformation,[],[f12])).
% 1.52/0.60  fof(f12,axiom,(
% 1.52/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.52/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.52/0.60  fof(f397,plain,(
% 1.52/0.60    ~spl4_21 | spl4_35 | ~spl4_33),
% 1.52/0.60    inference(avatar_split_clause,[],[f391,f381,f393,f279])).
% 1.52/0.60  fof(f279,plain,(
% 1.52/0.60    spl4_21 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.52/0.60  fof(f381,plain,(
% 1.52/0.60    spl4_33 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.52/0.60  fof(f391,plain,(
% 1.52/0.60    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_33),
% 1.52/0.60    inference(superposition,[],[f62,f383])).
% 1.52/0.60  fof(f383,plain,(
% 1.52/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_33),
% 1.52/0.60    inference(avatar_component_clause,[],[f381])).
% 1.52/0.60  fof(f62,plain,(
% 1.52/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.52/0.60    inference(cnf_transformation,[],[f29])).
% 1.52/0.60  fof(f29,plain,(
% 1.52/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.60    inference(ennf_transformation,[],[f10])).
% 1.52/0.60  fof(f10,axiom,(
% 1.52/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.52/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.52/0.60  fof(f384,plain,(
% 1.52/0.60    spl4_33 | ~spl4_22 | ~spl4_23 | ~spl4_31 | ~spl4_20 | ~spl4_21 | ~spl4_30),
% 1.52/0.60    inference(avatar_split_clause,[],[f378,f358,f279,f275,f362,f287,f283,f381])).
% 1.52/0.60  fof(f283,plain,(
% 1.52/0.60    spl4_22 <=> v1_funct_1(sK3)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.52/0.60  fof(f287,plain,(
% 1.52/0.60    spl4_23 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.52/0.60  fof(f362,plain,(
% 1.52/0.60    spl4_31 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 1.52/0.60  fof(f275,plain,(
% 1.52/0.60    spl4_20 <=> v1_funct_1(sK2)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.52/0.60  fof(f358,plain,(
% 1.52/0.60    spl4_30 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.52/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.52/0.60  fof(f378,plain,(
% 1.52/0.60    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.52/0.60    inference(resolution,[],[f65,f43])).
% 1.52/0.60  fof(f43,plain,(
% 1.52/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.52/0.60    inference(cnf_transformation,[],[f21])).
% 1.52/0.60  fof(f65,plain,(
% 1.52/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.52/0.60    inference(cnf_transformation,[],[f32])).
% 1.52/0.60  fof(f32,plain,(
% 1.52/0.60    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.52/0.60    inference(flattening,[],[f31])).
% 1.52/0.60  fof(f31,plain,(
% 1.52/0.60    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.52/0.60    inference(ennf_transformation,[],[f16])).
% 1.52/0.60  fof(f16,axiom,(
% 1.52/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.52/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.52/0.60  % (32370)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.52/0.60  % (32357)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.83/0.60  % (32372)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.83/0.60  % (32378)Refutation not found, incomplete strategy% (32378)------------------------------
% 1.83/0.60  % (32378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  fof(f377,plain,(
% 1.83/0.60    spl4_32),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f374])).
% 1.83/0.60  fof(f374,plain,(
% 1.83/0.60    $false | spl4_32),
% 1.83/0.60    inference(unit_resulting_resolution,[],[f72,f368])).
% 1.83/0.60  fof(f368,plain,(
% 1.83/0.60    ~v2_funct_1(k6_partfun1(sK0)) | spl4_32),
% 1.83/0.60    inference(avatar_component_clause,[],[f366])).
% 1.83/0.60  fof(f366,plain,(
% 1.83/0.60    spl4_32 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.83/0.60  fof(f72,plain,(
% 1.83/0.60    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.83/0.60    inference(definition_unfolding,[],[f48,f49])).
% 1.83/0.60  fof(f49,plain,(
% 1.83/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f15])).
% 1.83/0.60  fof(f15,axiom,(
% 1.83/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.83/0.60  fof(f48,plain,(
% 1.83/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f8])).
% 1.83/0.60  fof(f8,axiom,(
% 1.83/0.60    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 1.83/0.60  fof(f373,plain,(
% 1.83/0.60    spl4_31),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f372])).
% 1.83/0.60  fof(f372,plain,(
% 1.83/0.60    $false | spl4_31),
% 1.83/0.60    inference(subsumption_resolution,[],[f45,f364])).
% 1.83/0.60  fof(f364,plain,(
% 1.83/0.60    ~v1_funct_2(sK2,sK0,sK1) | spl4_31),
% 1.83/0.60    inference(avatar_component_clause,[],[f362])).
% 1.83/0.60  fof(f45,plain,(
% 1.83/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.83/0.60    inference(cnf_transformation,[],[f21])).
% 1.83/0.60  fof(f371,plain,(
% 1.83/0.60    spl4_30),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f370])).
% 1.83/0.60  fof(f370,plain,(
% 1.83/0.60    $false | spl4_30),
% 1.83/0.60    inference(subsumption_resolution,[],[f41,f360])).
% 1.83/0.60  fof(f360,plain,(
% 1.83/0.60    ~v1_funct_2(sK3,sK1,sK0) | spl4_30),
% 1.83/0.60    inference(avatar_component_clause,[],[f358])).
% 1.83/0.60  fof(f41,plain,(
% 1.83/0.60    v1_funct_2(sK3,sK1,sK0)),
% 1.83/0.60    inference(cnf_transformation,[],[f21])).
% 1.83/0.60  fof(f369,plain,(
% 1.83/0.60    spl4_2 | spl4_29 | ~spl4_20 | ~spl4_21 | ~spl4_30 | ~spl4_22 | ~spl4_23 | ~spl4_31 | ~spl4_32 | ~spl4_19),
% 1.83/0.60    inference(avatar_split_clause,[],[f352,f240,f366,f362,f287,f283,f358,f279,f275,f354,f84])).
% 1.83/0.60  fof(f84,plain,(
% 1.83/0.60    spl4_2 <=> v2_funct_1(sK2)),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.83/0.60  fof(f240,plain,(
% 1.83/0.60    spl4_19 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.83/0.60  fof(f352,plain,(
% 1.83/0.60    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~spl4_19),
% 1.83/0.60    inference(superposition,[],[f66,f242])).
% 1.83/0.60  fof(f242,plain,(
% 1.83/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_19),
% 1.83/0.60    inference(avatar_component_clause,[],[f240])).
% 1.83/0.60  fof(f66,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X3)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f34])).
% 1.83/0.60  fof(f34,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.83/0.60    inference(flattening,[],[f33])).
% 1.83/0.60  fof(f33,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.83/0.60    inference(ennf_transformation,[],[f17])).
% 1.83/0.60  fof(f17,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.83/0.60  fof(f313,plain,(
% 1.83/0.60    spl4_23),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f312])).
% 1.83/0.60  fof(f312,plain,(
% 1.83/0.60    $false | spl4_23),
% 1.83/0.60    inference(subsumption_resolution,[],[f46,f289])).
% 1.83/0.60  fof(f289,plain,(
% 1.83/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_23),
% 1.83/0.60    inference(avatar_component_clause,[],[f287])).
% 1.83/0.60  fof(f46,plain,(
% 1.83/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.83/0.60    inference(cnf_transformation,[],[f21])).
% 1.83/0.60  fof(f303,plain,(
% 1.83/0.60    spl4_22),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f302])).
% 1.83/0.60  fof(f302,plain,(
% 1.83/0.60    $false | spl4_22),
% 1.83/0.60    inference(subsumption_resolution,[],[f40,f285])).
% 1.83/0.60  fof(f285,plain,(
% 1.83/0.60    ~v1_funct_1(sK3) | spl4_22),
% 1.83/0.60    inference(avatar_component_clause,[],[f283])).
% 1.83/0.60  fof(f40,plain,(
% 1.83/0.60    v1_funct_1(sK3)),
% 1.83/0.60    inference(cnf_transformation,[],[f21])).
% 1.83/0.60  fof(f301,plain,(
% 1.83/0.60    spl4_21),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f300])).
% 1.83/0.60  fof(f300,plain,(
% 1.83/0.60    $false | spl4_21),
% 1.83/0.60    inference(subsumption_resolution,[],[f42,f281])).
% 1.83/0.60  fof(f281,plain,(
% 1.83/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_21),
% 1.83/0.60    inference(avatar_component_clause,[],[f279])).
% 1.83/0.60  fof(f298,plain,(
% 1.83/0.60    spl4_20),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f297])).
% 1.83/0.60  fof(f297,plain,(
% 1.83/0.60    $false | spl4_20),
% 1.83/0.60    inference(subsumption_resolution,[],[f44,f277])).
% 1.83/0.60  fof(f277,plain,(
% 1.83/0.60    ~v1_funct_1(sK2) | spl4_20),
% 1.83/0.60    inference(avatar_component_clause,[],[f275])).
% 1.83/0.60  fof(f44,plain,(
% 1.83/0.60    v1_funct_1(sK2)),
% 1.83/0.60    inference(cnf_transformation,[],[f21])).
% 1.83/0.60  fof(f268,plain,(
% 1.83/0.60    spl4_18),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f256])).
% 1.83/0.60  fof(f256,plain,(
% 1.83/0.60    $false | spl4_18),
% 1.83/0.60    inference(unit_resulting_resolution,[],[f44,f40,f42,f46,f238,f71])).
% 1.83/0.60  fof(f71,plain,(
% 1.83/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f38])).
% 1.83/0.60  fof(f38,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.83/0.60    inference(flattening,[],[f37])).
% 1.83/0.60  fof(f37,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.83/0.60    inference(ennf_transformation,[],[f13])).
% 1.83/0.60  fof(f13,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.83/0.60  fof(f238,plain,(
% 1.83/0.60    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_18),
% 1.83/0.60    inference(avatar_component_clause,[],[f236])).
% 1.83/0.60  fof(f236,plain,(
% 1.83/0.60    spl4_18 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.83/0.60  fof(f243,plain,(
% 1.83/0.60    ~spl4_18 | spl4_19),
% 1.83/0.60    inference(avatar_split_clause,[],[f234,f240,f236])).
% 1.83/0.60  fof(f234,plain,(
% 1.83/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.83/0.60    inference(resolution,[],[f225,f43])).
% 1.83/0.60  fof(f225,plain,(
% 1.83/0.60    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 1.83/0.60    inference(resolution,[],[f69,f51])).
% 1.83/0.60  fof(f51,plain,(
% 1.83/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f14])).
% 1.83/0.60  fof(f14,axiom,(
% 1.83/0.60    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.83/0.60  fof(f69,plain,(
% 1.83/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f36])).
% 1.83/0.60  fof(f36,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.83/0.60    inference(flattening,[],[f35])).
% 1.83/0.60  fof(f35,plain,(
% 1.83/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.83/0.60    inference(ennf_transformation,[],[f11])).
% 1.83/0.60  fof(f11,axiom,(
% 1.83/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.83/0.60  fof(f181,plain,(
% 1.83/0.60    spl4_11),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f180])).
% 1.83/0.60  fof(f180,plain,(
% 1.83/0.60    $false | spl4_11),
% 1.83/0.60    inference(unit_resulting_resolution,[],[f56,f46,f143,f54])).
% 1.83/0.60  fof(f54,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f24])).
% 1.83/0.60  fof(f24,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.83/0.60    inference(ennf_transformation,[],[f4])).
% 1.83/0.60  fof(f4,axiom,(
% 1.83/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.83/0.60  fof(f143,plain,(
% 1.83/0.60    ~v1_relat_1(sK2) | spl4_11),
% 1.83/0.60    inference(avatar_component_clause,[],[f142])).
% 1.83/0.60  fof(f142,plain,(
% 1.83/0.60    spl4_11 <=> v1_relat_1(sK2)),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.83/0.60  fof(f56,plain,(
% 1.83/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.83/0.60    inference(cnf_transformation,[],[f5])).
% 1.83/0.60  fof(f5,axiom,(
% 1.83/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.83/0.60  fof(f174,plain,(
% 1.83/0.60    spl4_2 | ~spl4_5 | ~spl4_11),
% 1.83/0.60    inference(avatar_split_clause,[],[f167,f142,f106,f84])).
% 1.83/0.60  fof(f106,plain,(
% 1.83/0.60    spl4_5 <=> v1_xboole_0(sK2)),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.83/0.60  fof(f167,plain,(
% 1.83/0.60    ~v1_relat_1(sK2) | ~v1_xboole_0(sK2) | v2_funct_1(sK2)),
% 1.83/0.60    inference(resolution,[],[f55,f44])).
% 1.83/0.60  fof(f55,plain,(
% 1.83/0.60    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0) | v2_funct_1(X0)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f26])).
% 1.83/0.60  fof(f26,plain,(
% 1.83/0.60    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.83/0.60    inference(flattening,[],[f25])).
% 1.83/0.60  fof(f25,plain,(
% 1.83/0.60    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 1.83/0.60    inference(ennf_transformation,[],[f7])).
% 1.83/0.60  fof(f7,axiom,(
% 1.83/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).
% 1.83/0.60  fof(f164,plain,(
% 1.83/0.60    spl4_10),
% 1.83/0.60    inference(avatar_contradiction_clause,[],[f161])).
% 1.83/0.60  fof(f161,plain,(
% 1.83/0.60    $false | spl4_10),
% 1.83/0.60    inference(unit_resulting_resolution,[],[f56,f139])).
% 1.83/0.60  fof(f139,plain,(
% 1.83/0.60    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_10),
% 1.83/0.60    inference(avatar_component_clause,[],[f137])).
% 1.83/0.60  fof(f137,plain,(
% 1.83/0.60    spl4_10 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.83/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.83/0.60  fof(f140,plain,(
% 1.83/0.60    spl4_9 | ~spl4_10),
% 1.83/0.60    inference(avatar_split_clause,[],[f128,f137,f133])).
% 1.83/0.60  fof(f128,plain,(
% 1.83/0.60    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.83/0.60    inference(resolution,[],[f54,f42])).
% 1.83/0.60  fof(f113,plain,(
% 1.83/0.60    spl4_5 | ~spl4_6),
% 1.83/0.60    inference(avatar_split_clause,[],[f94,f110,f106])).
% 1.83/0.60  fof(f94,plain,(
% 1.83/0.60    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2)),
% 1.83/0.60    inference(resolution,[],[f53,f46])).
% 1.83/0.60  fof(f53,plain,(
% 1.83/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.83/0.60    inference(cnf_transformation,[],[f23])).
% 1.83/0.60  fof(f23,plain,(
% 1.83/0.60    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.83/0.60    inference(ennf_transformation,[],[f3])).
% 1.83/0.60  fof(f3,axiom,(
% 1.83/0.60    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.83/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.83/0.60  fof(f87,plain,(
% 1.83/0.60    ~spl4_1 | ~spl4_2),
% 1.83/0.60    inference(avatar_split_clause,[],[f39,f84,f80])).
% 1.83/0.60  fof(f39,plain,(
% 1.83/0.60    ~v2_funct_1(sK2) | ~v2_funct_2(sK3,sK0)),
% 1.83/0.60    inference(cnf_transformation,[],[f21])).
% 1.83/0.60  % SZS output end Proof for theBenchmark
% 1.83/0.60  % (32368)------------------------------
% 1.83/0.60  % (32368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  % (32368)Termination reason: Refutation
% 1.83/0.60  
% 1.83/0.60  % (32368)Memory used [KB]: 6524
% 1.83/0.60  % (32368)Time elapsed: 0.165 s
% 1.83/0.60  % (32368)------------------------------
% 1.83/0.60  % (32368)------------------------------
% 1.83/0.61  % (32354)Success in time 0.241 s
%------------------------------------------------------------------------------
