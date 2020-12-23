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
% DateTime   : Thu Dec  3 13:01:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 253 expanded)
%              Number of leaves         :   36 (  84 expanded)
%              Depth                    :    8
%              Number of atoms          :  417 (1033 expanded)
%              Number of equality atoms :   43 (  56 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f145,f214,f231,f257,f259,f261,f270,f311,f313,f315,f320,f329,f342,f359,f363,f367,f396,f439])).

fof(f439,plain,
    ( spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f85,f435,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f88,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f88,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f72,f70])).

fof(f70,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f47,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f72,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f51,f48])).

fof(f51,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f435,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f144,f53])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f144,plain,
    ( ! [X5] : ~ r2_hidden(X5,sK2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_6
  <=> ! [X5] : ~ r2_hidden(X5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f85,plain,
    ( ~ v2_funct_1(sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f396,plain,
    ( spl5_5
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | spl5_5
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f46,f380])).

fof(f380,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_5
    | ~ spl5_16 ),
    inference(superposition,[],[f154,f298])).

fof(f298,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl5_16
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f154,plain,
    ( ~ v1_xboole_0(sK0)
    | spl5_5 ),
    inference(resolution,[],[f141,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f141,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl5_5
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f367,plain,(
    spl5_25 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl5_25 ),
    inference(subsumption_resolution,[],[f118,f358])).

fof(f358,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl5_25 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl5_25
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f118,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f61,f41])).

fof(f41,plain,(
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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f363,plain,(
    spl5_23 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | spl5_23 ),
    inference(subsumption_resolution,[],[f107,f349])).

fof(f349,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl5_23
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f107,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f58,f41])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f359,plain,
    ( spl5_1
    | ~ spl5_23
    | ~ spl5_25
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f345,f338,f356,f347,f79])).

fof(f79,plain,
    ( spl5_1
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f338,plain,
    ( spl5_22
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f345,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | v2_funct_2(sK3,sK0)
    | ~ spl5_22 ),
    inference(superposition,[],[f74,f340])).

fof(f340,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f338])).

fof(f74,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f342,plain,
    ( ~ spl5_12
    | spl5_22
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f336,f326,f338,f240])).

fof(f240,plain,
    ( spl5_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f326,plain,
    ( spl5_20
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f336,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_20 ),
    inference(superposition,[],[f59,f328])).

fof(f328,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f326])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f329,plain,
    ( spl5_20
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f321,f300,f240,f236,f304,f248,f244,f326])).

fof(f244,plain,
    ( spl5_13
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f248,plain,
    ( spl5_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f304,plain,
    ( spl5_18
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f236,plain,
    ( spl5_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f300,plain,
    ( spl5_17
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f321,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

% (1768)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f320,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl5_19 ),
    inference(unit_resulting_resolution,[],[f72,f310])).

fof(f310,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl5_19
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f315,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl5_18 ),
    inference(subsumption_resolution,[],[f44,f306])).

fof(f306,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl5_18 ),
    inference(avatar_component_clause,[],[f304])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f313,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | spl5_17 ),
    inference(subsumption_resolution,[],[f40,f302])).

fof(f302,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f300])).

fof(f40,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f311,plain,
    ( spl5_2
    | spl5_16
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_17
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f293,f211,f308,f304,f248,f244,f300,f240,f236,f296,f83])).

fof(f211,plain,
    ( spl5_10
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f293,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl5_10 ),
    inference(superposition,[],[f64,f213])).

fof(f213,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f211])).

% (1786)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f64,plain,(
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
    inference(cnf_transformation,[],[f33])).

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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f270,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl5_14 ),
    inference(subsumption_resolution,[],[f45,f250])).

fof(f250,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f248])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f261,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f260])).

% (1779)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f260,plain,
    ( $false
    | spl5_13 ),
    inference(subsumption_resolution,[],[f39,f246])).

fof(f246,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f244])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f259,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl5_12 ),
    inference(subsumption_resolution,[],[f41,f242])).

fof(f242,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f240])).

fof(f257,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl5_11 ),
    inference(subsumption_resolution,[],[f43,f238])).

fof(f238,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f236])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f231,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f43,f39,f41,f45,f209,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f209,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_9
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f214,plain,
    ( ~ spl5_9
    | spl5_10 ),
    inference(avatar_split_clause,[],[f203,f211,f207])).

fof(f203,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f193,f42])).

fof(f193,plain,(
    ! [X4,X3] :
      ( ~ r2_relset_1(X4,X4,X3,k6_partfun1(X4))
      | k6_partfun1(X4) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4))) ) ),
    inference(resolution,[],[f67,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f145,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f128,f143,f139])).

fof(f128,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f63,f45])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f86,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f38,f83,f79])).

fof(f38,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:12:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (1764)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (1762)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (1772)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (1773)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (1760)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (1759)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (1780)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (1761)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (1775)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (1763)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (1782)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (1774)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (1785)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (1765)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (1766)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (1769)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (1772)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (1777)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (1787)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (1781)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.55  % (1776)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.55  % (1784)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f440,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(avatar_sat_refutation,[],[f86,f145,f214,f231,f257,f259,f261,f270,f311,f313,f315,f320,f329,f342,f359,f363,f367,f396,f439])).
% 1.42/0.55  fof(f439,plain,(
% 1.42/0.55    spl5_2 | ~spl5_6),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f436])).
% 1.42/0.55  fof(f436,plain,(
% 1.42/0.55    $false | (spl5_2 | ~spl5_6)),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f85,f435,f93])).
% 1.42/0.55  fof(f93,plain,(
% 1.42/0.55    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) )),
% 1.42/0.55    inference(superposition,[],[f88,f52])).
% 1.42/0.55  fof(f52,plain,(
% 1.42/0.55    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f22])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.42/0.55  fof(f88,plain,(
% 1.42/0.55    v2_funct_1(k1_xboole_0)),
% 1.42/0.55    inference(superposition,[],[f72,f70])).
% 1.42/0.55  fof(f70,plain,(
% 1.42/0.55    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.42/0.55    inference(definition_unfolding,[],[f47,f48])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f15])).
% 1.42/0.55  fof(f15,axiom,(
% 1.42/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.42/0.55    inference(cnf_transformation,[],[f6])).
% 1.42/0.55  fof(f6,axiom,(
% 1.42/0.55    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.42/0.55  fof(f72,plain,(
% 1.42/0.55    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f51,f48])).
% 1.42/0.55  fof(f51,plain,(
% 1.42/0.55    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.42/0.55  fof(f435,plain,(
% 1.42/0.55    v1_xboole_0(sK2) | ~spl5_6),
% 1.42/0.55    inference(resolution,[],[f144,f53])).
% 1.42/0.55  fof(f53,plain,(
% 1.42/0.55    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.42/0.55  fof(f144,plain,(
% 1.42/0.55    ( ! [X5] : (~r2_hidden(X5,sK2)) ) | ~spl5_6),
% 1.42/0.55    inference(avatar_component_clause,[],[f143])).
% 1.42/0.55  fof(f143,plain,(
% 1.42/0.55    spl5_6 <=> ! [X5] : ~r2_hidden(X5,sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.42/0.55  fof(f85,plain,(
% 1.42/0.55    ~v2_funct_1(sK2) | spl5_2),
% 1.42/0.55    inference(avatar_component_clause,[],[f83])).
% 1.42/0.55  fof(f83,plain,(
% 1.42/0.55    spl5_2 <=> v2_funct_1(sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.42/0.55  fof(f396,plain,(
% 1.42/0.55    spl5_5 | ~spl5_16),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f391])).
% 1.42/0.55  fof(f391,plain,(
% 1.42/0.55    $false | (spl5_5 | ~spl5_16)),
% 1.42/0.55    inference(subsumption_resolution,[],[f46,f380])).
% 1.42/0.55  fof(f380,plain,(
% 1.42/0.55    ~v1_xboole_0(k1_xboole_0) | (spl5_5 | ~spl5_16)),
% 1.42/0.55    inference(superposition,[],[f154,f298])).
% 1.42/0.55  fof(f298,plain,(
% 1.42/0.55    k1_xboole_0 = sK0 | ~spl5_16),
% 1.42/0.55    inference(avatar_component_clause,[],[f296])).
% 1.42/0.55  fof(f296,plain,(
% 1.42/0.55    spl5_16 <=> k1_xboole_0 = sK0),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.42/0.55  fof(f154,plain,(
% 1.42/0.55    ~v1_xboole_0(sK0) | spl5_5),
% 1.42/0.55    inference(resolution,[],[f141,f55])).
% 1.42/0.55  fof(f55,plain,(
% 1.42/0.55    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.42/0.55    inference(ennf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.42/0.55  fof(f141,plain,(
% 1.42/0.55    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl5_5),
% 1.42/0.55    inference(avatar_component_clause,[],[f139])).
% 1.42/0.55  fof(f139,plain,(
% 1.42/0.55    spl5_5 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.42/0.55  fof(f46,plain,(
% 1.42/0.55    v1_xboole_0(k1_xboole_0)),
% 1.42/0.55    inference(cnf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    v1_xboole_0(k1_xboole_0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.42/0.55  fof(f367,plain,(
% 1.42/0.55    spl5_25),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f364])).
% 1.42/0.55  fof(f364,plain,(
% 1.42/0.55    $false | spl5_25),
% 1.42/0.55    inference(subsumption_resolution,[],[f118,f358])).
% 1.42/0.55  fof(f358,plain,(
% 1.42/0.55    ~v5_relat_1(sK3,sK0) | spl5_25),
% 1.42/0.55    inference(avatar_component_clause,[],[f356])).
% 1.42/0.55  fof(f356,plain,(
% 1.42/0.55    spl5_25 <=> v5_relat_1(sK3,sK0)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.42/0.55  fof(f118,plain,(
% 1.42/0.55    v5_relat_1(sK3,sK0)),
% 1.42/0.55    inference(resolution,[],[f61,f41])).
% 1.42/0.55  fof(f41,plain,(
% 1.42/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.42/0.55    inference(flattening,[],[f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.42/0.55    inference(ennf_transformation,[],[f19])).
% 1.42/0.55  fof(f19,negated_conjecture,(
% 1.42/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.42/0.55    inference(negated_conjecture,[],[f18])).
% 1.42/0.55  fof(f18,conjecture,(
% 1.42/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.42/0.55  fof(f61,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f28])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.42/0.55  fof(f363,plain,(
% 1.42/0.55    spl5_23),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f360])).
% 1.42/0.55  fof(f360,plain,(
% 1.42/0.55    $false | spl5_23),
% 1.42/0.55    inference(subsumption_resolution,[],[f107,f349])).
% 1.42/0.55  fof(f349,plain,(
% 1.42/0.55    ~v1_relat_1(sK3) | spl5_23),
% 1.42/0.55    inference(avatar_component_clause,[],[f347])).
% 1.42/0.55  fof(f347,plain,(
% 1.42/0.55    spl5_23 <=> v1_relat_1(sK3)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.42/0.55  fof(f107,plain,(
% 1.42/0.55    v1_relat_1(sK3)),
% 1.42/0.55    inference(resolution,[],[f58,f41])).
% 1.42/0.55  fof(f58,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f26])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.42/0.55  fof(f359,plain,(
% 1.42/0.55    spl5_1 | ~spl5_23 | ~spl5_25 | ~spl5_22),
% 1.42/0.55    inference(avatar_split_clause,[],[f345,f338,f356,f347,f79])).
% 1.42/0.55  fof(f79,plain,(
% 1.42/0.55    spl5_1 <=> v2_funct_2(sK3,sK0)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.42/0.55  fof(f338,plain,(
% 1.42/0.55    spl5_22 <=> sK0 = k2_relat_1(sK3)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.42/0.55  fof(f345,plain,(
% 1.42/0.55    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | v2_funct_2(sK3,sK0) | ~spl5_22),
% 1.42/0.55    inference(superposition,[],[f74,f340])).
% 1.42/0.55  fof(f340,plain,(
% 1.42/0.55    sK0 = k2_relat_1(sK3) | ~spl5_22),
% 1.42/0.55    inference(avatar_component_clause,[],[f338])).
% 1.42/0.55  fof(f74,plain,(
% 1.42/0.55    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 1.42/0.55    inference(equality_resolution,[],[f56])).
% 1.42/0.55  fof(f56,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f25])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.42/0.55    inference(flattening,[],[f24])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.42/0.55    inference(ennf_transformation,[],[f13])).
% 1.42/0.55  fof(f13,axiom,(
% 1.42/0.55    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.42/0.55  fof(f342,plain,(
% 1.42/0.55    ~spl5_12 | spl5_22 | ~spl5_20),
% 1.42/0.55    inference(avatar_split_clause,[],[f336,f326,f338,f240])).
% 1.42/0.55  fof(f240,plain,(
% 1.42/0.55    spl5_12 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.42/0.55  fof(f326,plain,(
% 1.42/0.55    spl5_20 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.42/0.55  fof(f336,plain,(
% 1.42/0.55    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_20),
% 1.42/0.55    inference(superposition,[],[f59,f328])).
% 1.42/0.55  fof(f328,plain,(
% 1.42/0.55    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl5_20),
% 1.42/0.55    inference(avatar_component_clause,[],[f326])).
% 1.42/0.55  fof(f59,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f27])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(ennf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.42/0.55  fof(f329,plain,(
% 1.42/0.55    spl5_20 | ~spl5_13 | ~spl5_14 | ~spl5_18 | ~spl5_11 | ~spl5_12 | ~spl5_17),
% 1.42/0.55    inference(avatar_split_clause,[],[f321,f300,f240,f236,f304,f248,f244,f326])).
% 1.42/0.55  fof(f244,plain,(
% 1.42/0.55    spl5_13 <=> v1_funct_1(sK3)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.42/0.55  fof(f248,plain,(
% 1.42/0.55    spl5_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.42/0.55  fof(f304,plain,(
% 1.42/0.55    spl5_18 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.42/0.55  fof(f236,plain,(
% 1.42/0.55    spl5_11 <=> v1_funct_1(sK2)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.42/0.55  fof(f300,plain,(
% 1.42/0.55    spl5_17 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.42/0.55  fof(f321,plain,(
% 1.42/0.55    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.42/0.55    inference(resolution,[],[f62,f42])).
% 1.42/0.55  fof(f42,plain,(
% 1.42/0.55    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f62,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f30])).
% 1.42/0.55  % (1768)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.42/0.55    inference(flattening,[],[f29])).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.42/0.55    inference(ennf_transformation,[],[f16])).
% 1.42/0.55  fof(f16,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.42/0.55  fof(f320,plain,(
% 1.42/0.55    spl5_19),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f316])).
% 1.42/0.55  fof(f316,plain,(
% 1.42/0.55    $false | spl5_19),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f72,f310])).
% 1.42/0.55  fof(f310,plain,(
% 1.42/0.55    ~v2_funct_1(k6_partfun1(sK0)) | spl5_19),
% 1.42/0.55    inference(avatar_component_clause,[],[f308])).
% 1.42/0.55  fof(f308,plain,(
% 1.42/0.55    spl5_19 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.42/0.55  fof(f315,plain,(
% 1.42/0.55    spl5_18),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f314])).
% 1.42/0.55  fof(f314,plain,(
% 1.42/0.55    $false | spl5_18),
% 1.42/0.55    inference(subsumption_resolution,[],[f44,f306])).
% 1.42/0.55  fof(f306,plain,(
% 1.42/0.55    ~v1_funct_2(sK2,sK0,sK1) | spl5_18),
% 1.42/0.55    inference(avatar_component_clause,[],[f304])).
% 1.42/0.55  fof(f44,plain,(
% 1.42/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f313,plain,(
% 1.42/0.55    spl5_17),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f312])).
% 1.42/0.55  fof(f312,plain,(
% 1.42/0.55    $false | spl5_17),
% 1.42/0.55    inference(subsumption_resolution,[],[f40,f302])).
% 1.42/0.55  fof(f302,plain,(
% 1.42/0.55    ~v1_funct_2(sK3,sK1,sK0) | spl5_17),
% 1.42/0.55    inference(avatar_component_clause,[],[f300])).
% 1.42/0.55  fof(f40,plain,(
% 1.42/0.55    v1_funct_2(sK3,sK1,sK0)),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f311,plain,(
% 1.42/0.55    spl5_2 | spl5_16 | ~spl5_11 | ~spl5_12 | ~spl5_17 | ~spl5_13 | ~spl5_14 | ~spl5_18 | ~spl5_19 | ~spl5_10),
% 1.42/0.55    inference(avatar_split_clause,[],[f293,f211,f308,f304,f248,f244,f300,f240,f236,f296,f83])).
% 1.42/0.55  fof(f211,plain,(
% 1.42/0.55    spl5_10 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.42/0.55  fof(f293,plain,(
% 1.42/0.55    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~spl5_10),
% 1.42/0.55    inference(superposition,[],[f64,f213])).
% 1.42/0.55  fof(f213,plain,(
% 1.42/0.55    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl5_10),
% 1.42/0.55    inference(avatar_component_clause,[],[f211])).
% 1.42/0.55  % (1786)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.42/0.55  fof(f64,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X3)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f33])).
% 1.42/0.55  fof(f33,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.42/0.55    inference(flattening,[],[f32])).
% 1.42/0.55  fof(f32,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.42/0.55    inference(ennf_transformation,[],[f17])).
% 1.42/0.55  fof(f17,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.42/0.55  fof(f270,plain,(
% 1.42/0.55    spl5_14),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f269])).
% 1.42/0.55  fof(f269,plain,(
% 1.42/0.55    $false | spl5_14),
% 1.42/0.55    inference(subsumption_resolution,[],[f45,f250])).
% 1.42/0.55  fof(f250,plain,(
% 1.42/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_14),
% 1.42/0.55    inference(avatar_component_clause,[],[f248])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f261,plain,(
% 1.42/0.55    spl5_13),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f260])).
% 1.42/0.55  % (1779)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.55  fof(f260,plain,(
% 1.42/0.55    $false | spl5_13),
% 1.42/0.55    inference(subsumption_resolution,[],[f39,f246])).
% 1.42/0.55  fof(f246,plain,(
% 1.42/0.55    ~v1_funct_1(sK3) | spl5_13),
% 1.42/0.55    inference(avatar_component_clause,[],[f244])).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    v1_funct_1(sK3)),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f259,plain,(
% 1.42/0.55    spl5_12),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f258])).
% 1.42/0.55  fof(f258,plain,(
% 1.42/0.55    $false | spl5_12),
% 1.42/0.55    inference(subsumption_resolution,[],[f41,f242])).
% 1.42/0.55  fof(f242,plain,(
% 1.42/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_12),
% 1.42/0.55    inference(avatar_component_clause,[],[f240])).
% 1.42/0.55  fof(f257,plain,(
% 1.42/0.55    spl5_11),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f256])).
% 1.42/0.55  fof(f256,plain,(
% 1.42/0.55    $false | spl5_11),
% 1.42/0.55    inference(subsumption_resolution,[],[f43,f238])).
% 1.42/0.55  fof(f238,plain,(
% 1.42/0.55    ~v1_funct_1(sK2) | spl5_11),
% 1.42/0.55    inference(avatar_component_clause,[],[f236])).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    v1_funct_1(sK2)),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  fof(f231,plain,(
% 1.42/0.55    spl5_9),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f219])).
% 1.42/0.55  fof(f219,plain,(
% 1.42/0.55    $false | spl5_9),
% 1.42/0.55    inference(unit_resulting_resolution,[],[f43,f39,f41,f45,f209,f69])).
% 1.42/0.55  fof(f69,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f37])).
% 1.42/0.55  fof(f37,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.42/0.55    inference(flattening,[],[f36])).
% 1.42/0.55  fof(f36,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.42/0.55    inference(ennf_transformation,[],[f14])).
% 1.42/0.55  fof(f14,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.42/0.55  fof(f209,plain,(
% 1.42/0.55    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_9),
% 1.42/0.55    inference(avatar_component_clause,[],[f207])).
% 1.42/0.55  fof(f207,plain,(
% 1.42/0.55    spl5_9 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.42/0.55  fof(f214,plain,(
% 1.42/0.55    ~spl5_9 | spl5_10),
% 1.42/0.55    inference(avatar_split_clause,[],[f203,f211,f207])).
% 1.42/0.55  fof(f203,plain,(
% 1.42/0.55    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.42/0.55    inference(resolution,[],[f193,f42])).
% 1.42/0.55  fof(f193,plain,(
% 1.42/0.55    ( ! [X4,X3] : (~r2_relset_1(X4,X4,X3,k6_partfun1(X4)) | k6_partfun1(X4) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X4)))) )),
% 1.42/0.55    inference(resolution,[],[f67,f71])).
% 1.42/0.55  fof(f71,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f49,f48])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,axiom,(
% 1.42/0.55    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.42/0.55  fof(f67,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f35])).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.55    inference(flattening,[],[f34])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.42/0.55    inference(ennf_transformation,[],[f11])).
% 1.42/0.55  fof(f11,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.42/0.55  fof(f145,plain,(
% 1.42/0.55    ~spl5_5 | spl5_6),
% 1.42/0.55    inference(avatar_split_clause,[],[f128,f143,f139])).
% 1.42/0.55  fof(f128,plain,(
% 1.42/0.55    ( ! [X5] : (~r2_hidden(X5,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) )),
% 1.42/0.55    inference(resolution,[],[f63,f45])).
% 1.42/0.55  fof(f63,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f31])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.42/0.55    inference(ennf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.42/0.55  fof(f86,plain,(
% 1.42/0.55    ~spl5_1 | ~spl5_2),
% 1.42/0.55    inference(avatar_split_clause,[],[f38,f83,f79])).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ~v2_funct_1(sK2) | ~v2_funct_2(sK3,sK0)),
% 1.42/0.55    inference(cnf_transformation,[],[f21])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (1772)------------------------------
% 1.42/0.55  % (1772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (1772)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (1772)Memory used [KB]: 6524
% 1.42/0.55  % (1772)Time elapsed: 0.123 s
% 1.42/0.55  % (1772)------------------------------
% 1.42/0.55  % (1772)------------------------------
% 1.42/0.55  % (1770)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.42/0.56  % (1758)Success in time 0.193 s
%------------------------------------------------------------------------------
