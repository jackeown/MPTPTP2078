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
% DateTime   : Thu Dec  3 13:03:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 231 expanded)
%              Number of leaves         :   37 (  98 expanded)
%              Depth                    :    9
%              Number of atoms          :  471 (1124 expanded)
%              Number of equality atoms :   74 ( 141 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f467,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f126,f131,f136,f146,f190,f215,f270,f317,f331,f374,f378,f439,f443,f464])).

fof(f464,plain,(
    ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f206,f185])).

fof(f185,plain,
    ( ! [X1] : ~ v1_relat_1(X1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl6_16
  <=> ! [X1] : ~ v1_relat_1(X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f206,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(resolution,[],[f149,f64])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f149,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_zfmisc_1(X0,X0))
      | v1_relat_1(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f79,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f65,f57])).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f443,plain,
    ( ~ spl6_20
    | ~ spl6_45 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl6_20
    | ~ spl6_45 ),
    inference(unit_resulting_resolution,[],[f63,f438,f214])).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | r2_hidden(X1,X0) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl6_20
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

% (11808)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f438,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl6_45
  <=> r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f63,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f439,plain,
    ( spl6_45
    | ~ spl6_29
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f392,f280,f267,f436])).

fof(f267,plain,
    ( spl6_29
  <=> r2_hidden(sK4(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

% (11815)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (11806)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (11825)Refutation not found, incomplete strategy% (11825)------------------------------
% (11825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11825)Termination reason: Refutation not found, incomplete strategy

% (11825)Memory used [KB]: 11001
% (11825)Time elapsed: 0.123 s
% (11825)------------------------------
% (11825)------------------------------
% (11822)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (11807)Refutation not found, incomplete strategy% (11807)------------------------------
% (11807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11807)Termination reason: Refutation not found, incomplete strategy

% (11807)Memory used [KB]: 11001
% (11807)Time elapsed: 0.142 s
% (11807)------------------------------
% (11807)------------------------------
fof(f280,plain,
    ( spl6_31
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f392,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl6_29
    | ~ spl6_31 ),
    inference(superposition,[],[f269,f282])).

fof(f282,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f280])).

fof(f269,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f267])).

fof(f378,plain,(
    spl6_39 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl6_39 ),
    inference(unit_resulting_resolution,[],[f82,f373])).

fof(f373,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl6_39 ),
    inference(avatar_component_clause,[],[f371])).

fof(f371,plain,
    ( spl6_39
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f82,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f54,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f374,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | spl6_3
    | spl6_31
    | ~ spl6_39
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f366,f314,f371,f280,f103,f128,f118,f98,f123,f113,f93])).

fof(f93,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f113,plain,
    ( spl6_5
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f123,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f98,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f118,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f128,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f103,plain,
    ( spl6_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f314,plain,
    ( spl6_37
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f366,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl6_37 ),
    inference(superposition,[],[f52,f316])).

fof(f316,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f314])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f331,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | spl6_36 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | spl6_36 ),
    inference(unit_resulting_resolution,[],[f95,f100,f125,f130,f312,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f312,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_36 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl6_36
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f130,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f125,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f100,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f95,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f317,plain,
    ( ~ spl6_36
    | spl6_37
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f307,f143,f314,f310])).

fof(f143,plain,
    ( spl6_11
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f307,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl6_11 ),
    inference(resolution,[],[f238,f145])).

fof(f145,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f238,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f55,f83])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f270,plain,
    ( ~ spl6_1
    | ~ spl6_5
    | spl6_3
    | spl6_4
    | spl6_29
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f253,f123,f267,f108,f103,f113,f93])).

fof(f108,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f253,plain,
    ( r2_hidden(sK4(sK0,sK2),sK0)
    | k1_xboole_0 = sK1
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl6_7 ),
    inference(resolution,[],[f68,f125])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X2),X0)
      | k1_xboole_0 = X1
      | v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X2)
          | ( sK4(X0,X2) != sK5(X0,X2)
            & k1_funct_1(X2,sK4(X0,X2)) = k1_funct_1(X2,sK5(X0,X2))
            & r2_hidden(sK5(X0,X2),X0)
            & r2_hidden(sK4(X0,X2),X0) ) )
        & ( ! [X5,X6] :
              ( X5 = X6
              | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
              | ~ r2_hidden(X6,X0)
              | ~ r2_hidden(X5,X0) )
          | ~ v2_funct_1(X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ? [X3,X4] :
          ( X3 != X4
          & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
          & r2_hidden(X4,X0)
          & r2_hidden(X3,X0) )
     => ( sK4(X0,X2) != sK5(X0,X2)
        & k1_funct_1(X2,sK4(X0,X2)) = k1_funct_1(X2,sK5(X0,X2))
        & r2_hidden(sK5(X0,X2),X0)
        & r2_hidden(sK4(X0,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X2)
          | ? [X3,X4] :
              ( X3 != X4
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              & r2_hidden(X4,X0)
              & r2_hidden(X3,X0) ) )
        & ( ! [X5,X6] :
              ( X5 = X6
              | k1_funct_1(X2,X5) != k1_funct_1(X2,X6)
              | ~ r2_hidden(X6,X0)
              | ~ r2_hidden(X5,X0) )
          | ~ v2_funct_1(X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_funct_1(X2)
          | ? [X3,X4] :
              ( X3 != X4
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              & r2_hidden(X4,X0)
              & r2_hidden(X3,X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X3,X0) )
          | ~ v2_funct_1(X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                & r2_hidden(X4,X0)
                & r2_hidden(X3,X0) )
             => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).

fof(f215,plain,
    ( ~ spl6_17
    | spl6_20
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f182,f133,f213,f187])).

fof(f187,plain,
    ( spl6_17
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f133,plain,
    ( spl6_9
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | r2_hidden(X1,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f181,f135])).

fof(f135,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
      | r2_hidden(X1,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f76,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f190,plain,
    ( spl6_16
    | spl6_17 ),
    inference(avatar_split_clause,[],[f150,f187,f184])).

fof(f150,plain,(
    ! [X1] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f79,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f146,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f50,f143])).

fof(f50,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f34,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ~ v2_funct_1(X2)
        & ? [X3] :
            ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(sK2)
      & ? [X3] :
          ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).

fof(f136,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f80,f133])).

fof(f80,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f131,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f49,f128])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f126,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f45,f123])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f121,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f48,f118])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f116,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f44,f113])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f111,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f46,f108])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f51,f103])).

fof(f51,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f47,f98])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f43,f93])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:46:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (11820)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (11797)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (11798)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (11804)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (11817)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (11809)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (11805)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (11801)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (11821)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (11825)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (11819)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (11807)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (11813)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (11800)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (11811)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (11813)Refutation not found, incomplete strategy% (11813)------------------------------
% 0.21/0.54  % (11813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11813)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11813)Memory used [KB]: 10746
% 0.21/0.54  % (11813)Time elapsed: 0.121 s
% 0.21/0.54  % (11813)------------------------------
% 0.21/0.54  % (11813)------------------------------
% 0.21/0.54  % (11820)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (11803)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (11812)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (11826)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (11818)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (11799)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (11802)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (11824)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (11816)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (11824)Refutation not found, incomplete strategy% (11824)------------------------------
% 0.21/0.55  % (11824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11824)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11824)Memory used [KB]: 6268
% 0.21/0.55  % (11824)Time elapsed: 0.126 s
% 0.21/0.55  % (11824)------------------------------
% 0.21/0.55  % (11824)------------------------------
% 0.21/0.55  % (11814)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (11823)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (11810)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f467,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f126,f131,f136,f146,f190,f215,f270,f317,f331,f374,f378,f439,f443,f464])).
% 0.21/0.55  fof(f464,plain,(
% 0.21/0.55    ~spl6_16),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f460])).
% 0.21/0.55  fof(f460,plain,(
% 0.21/0.55    $false | ~spl6_16),
% 0.21/0.55    inference(subsumption_resolution,[],[f206,f185])).
% 0.21/0.55  fof(f185,plain,(
% 0.21/0.55    ( ! [X1] : (~v1_relat_1(X1)) ) | ~spl6_16),
% 0.21/0.55    inference(avatar_component_clause,[],[f184])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    spl6_16 <=> ! [X1] : ~v1_relat_1(X1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.55    inference(resolution,[],[f149,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_relat_1(k2_zfmisc_1(X0,X0)) | v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.55    inference(resolution,[],[f79,f83])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f65,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.55  fof(f443,plain,(
% 0.21/0.55    ~spl6_20 | ~spl6_45),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f440])).
% 0.21/0.55  fof(f440,plain,(
% 0.21/0.55    $false | (~spl6_20 | ~spl6_45)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f63,f438,f214])).
% 0.21/0.55  fof(f214,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) ) | ~spl6_20),
% 0.21/0.55    inference(avatar_component_clause,[],[f213])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    spl6_20 <=> ! [X1,X0] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.55  % (11808)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  fof(f438,plain,(
% 0.21/0.55    r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0) | ~spl6_45),
% 0.21/0.55    inference(avatar_component_clause,[],[f436])).
% 0.21/0.55  fof(f436,plain,(
% 0.21/0.55    spl6_45 <=> r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.55  fof(f439,plain,(
% 0.21/0.55    spl6_45 | ~spl6_29 | ~spl6_31),
% 0.21/0.55    inference(avatar_split_clause,[],[f392,f280,f267,f436])).
% 0.21/0.56  fof(f267,plain,(
% 0.21/0.56    spl6_29 <=> r2_hidden(sK4(sK0,sK2),sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.56  % (11815)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (11806)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (11825)Refutation not found, incomplete strategy% (11825)------------------------------
% 0.21/0.56  % (11825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11825)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11825)Memory used [KB]: 11001
% 0.21/0.56  % (11825)Time elapsed: 0.123 s
% 0.21/0.56  % (11825)------------------------------
% 0.21/0.56  % (11825)------------------------------
% 0.21/0.56  % (11822)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (11807)Refutation not found, incomplete strategy% (11807)------------------------------
% 0.21/0.56  % (11807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11807)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11807)Memory used [KB]: 11001
% 0.21/0.56  % (11807)Time elapsed: 0.142 s
% 0.21/0.56  % (11807)------------------------------
% 0.21/0.56  % (11807)------------------------------
% 0.21/0.56  fof(f280,plain,(
% 0.21/0.56    spl6_31 <=> k1_xboole_0 = sK0),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.56  fof(f392,plain,(
% 0.21/0.56    r2_hidden(sK4(k1_xboole_0,sK2),k1_xboole_0) | (~spl6_29 | ~spl6_31)),
% 0.21/0.56    inference(superposition,[],[f269,f282])).
% 0.21/0.56  fof(f282,plain,(
% 0.21/0.56    k1_xboole_0 = sK0 | ~spl6_31),
% 0.21/0.56    inference(avatar_component_clause,[],[f280])).
% 0.21/0.56  fof(f269,plain,(
% 0.21/0.56    r2_hidden(sK4(sK0,sK2),sK0) | ~spl6_29),
% 0.21/0.56    inference(avatar_component_clause,[],[f267])).
% 0.21/0.56  fof(f378,plain,(
% 0.21/0.56    spl6_39),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f375])).
% 0.21/0.56  fof(f375,plain,(
% 0.21/0.56    $false | spl6_39),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f82,f373])).
% 0.21/0.56  fof(f373,plain,(
% 0.21/0.56    ~v2_funct_1(k6_partfun1(sK0)) | spl6_39),
% 0.21/0.56    inference(avatar_component_clause,[],[f371])).
% 0.21/0.56  fof(f371,plain,(
% 0.21/0.56    spl6_39 <=> v2_funct_1(k6_partfun1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f54,f57])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 0.21/0.56  fof(f374,plain,(
% 0.21/0.56    ~spl6_1 | ~spl6_5 | ~spl6_7 | ~spl6_2 | ~spl6_6 | ~spl6_8 | spl6_3 | spl6_31 | ~spl6_39 | ~spl6_37),
% 0.21/0.56    inference(avatar_split_clause,[],[f366,f314,f371,f280,f103,f128,f118,f98,f123,f113,f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    spl6_1 <=> v1_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    spl6_5 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    spl6_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    spl6_2 <=> v1_funct_1(sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    spl6_6 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    spl6_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    spl6_3 <=> v2_funct_1(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.56  fof(f314,plain,(
% 0.21/0.56    spl6_37 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.56  fof(f366,plain,(
% 0.21/0.56    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl6_37),
% 0.21/0.56    inference(superposition,[],[f52,f316])).
% 0.21/0.56  fof(f316,plain,(
% 0.21/0.56    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl6_37),
% 0.21/0.56    inference(avatar_component_clause,[],[f314])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.56    inference(ennf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 0.21/0.56  fof(f331,plain,(
% 0.21/0.56    ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | spl6_36),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f318])).
% 0.21/0.56  fof(f318,plain,(
% 0.21/0.56    $false | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | spl6_36)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f95,f100,f125,f130,f312,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.56  fof(f312,plain,(
% 0.21/0.56    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_36),
% 0.21/0.56    inference(avatar_component_clause,[],[f310])).
% 0.21/0.56  fof(f310,plain,(
% 0.21/0.56    spl6_36 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.56  fof(f130,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f128])).
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f123])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    v1_funct_1(sK3) | ~spl6_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f98])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    v1_funct_1(sK2) | ~spl6_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f93])).
% 0.21/0.56  fof(f317,plain,(
% 0.21/0.56    ~spl6_36 | spl6_37 | ~spl6_11),
% 0.21/0.56    inference(avatar_split_clause,[],[f307,f143,f314,f310])).
% 0.21/0.56  fof(f143,plain,(
% 0.21/0.56    spl6_11 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.56  fof(f307,plain,(
% 0.21/0.56    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl6_11),
% 0.21/0.56    inference(resolution,[],[f238,f145])).
% 0.21/0.56  fof(f145,plain,(
% 0.21/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl6_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f143])).
% 0.21/0.56  fof(f238,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.21/0.56    inference(resolution,[],[f55,f83])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(nnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.56  fof(f270,plain,(
% 0.21/0.56    ~spl6_1 | ~spl6_5 | spl6_3 | spl6_4 | spl6_29 | ~spl6_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f253,f123,f267,f108,f103,f113,f93])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    spl6_4 <=> k1_xboole_0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.56  fof(f253,plain,(
% 0.21/0.56    r2_hidden(sK4(sK0,sK2),sK0) | k1_xboole_0 = sK1 | v2_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl6_7),
% 0.21/0.56    inference(resolution,[],[f68,f125])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X2),X0) | k1_xboole_0 = X1 | v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((v2_funct_1(X2) | (sK4(X0,X2) != sK5(X0,X2) & k1_funct_1(X2,sK4(X0,X2)) = k1_funct_1(X2,sK5(X0,X2)) & r2_hidden(sK5(X0,X2),X0) & r2_hidden(sK4(X0,X2),X0))) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | ~v2_funct_1(X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f38,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X2,X0] : (? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => (sK4(X0,X2) != sK5(X0,X2) & k1_funct_1(X2,sK4(X0,X2)) = k1_funct_1(X2,sK5(X0,X2)) & r2_hidden(sK5(X0,X2),X0) & r2_hidden(sK4(X0,X2),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((v2_funct_1(X2) | ? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0))) & (! [X5,X6] : (X5 = X6 | k1_funct_1(X2,X5) != k1_funct_1(X2,X6) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X0)) | ~v2_funct_1(X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.56    inference(rectify,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((v2_funct_1(X2) | ? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_funct_1(X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).
% 0.21/0.56  fof(f215,plain,(
% 0.21/0.56    ~spl6_17 | spl6_20 | ~spl6_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f182,f133,f213,f187])).
% 0.21/0.56  fof(f187,plain,(
% 0.21/0.56    spl6_17 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    spl6_9 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl6_9),
% 0.21/0.56    inference(forward_demodulation,[],[f181,f135])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f133])).
% 0.21/0.56  fof(f181,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k1_xboole_0)) | r2_hidden(X1,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.56    inference(superposition,[],[f76,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.56  fof(f190,plain,(
% 0.21/0.56    spl6_16 | spl6_17),
% 0.21/0.56    inference(avatar_split_clause,[],[f150,f187,f184])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    ( ! [X1] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(resolution,[],[f79,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    spl6_11),
% 0.21/0.56    inference(avatar_split_clause,[],[f50,f143])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ~v2_funct_1(sK2) & (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f34,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (~v2_funct_1(sK2) & ? [X3] : (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ? [X3] : (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ? [X0,X1,X2] : ((~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 0.21/0.56    inference(negated_conjecture,[],[f17])).
% 0.21/0.56  fof(f17,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_funct_2)).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    spl6_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f80,f133])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    spl6_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f49,f128])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    spl6_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f45,f123])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    spl6_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f48,f118])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    spl6_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f44,f113])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    ~spl6_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f46,f108])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    k1_xboole_0 != sK1),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ~spl6_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f51,f103])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ~v2_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    spl6_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f47,f98])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    v1_funct_1(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    spl6_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f43,f93])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    v1_funct_1(sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f35])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (11820)------------------------------
% 0.21/0.56  % (11820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11820)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (11820)Memory used [KB]: 11257
% 0.21/0.56  % (11820)Time elapsed: 0.126 s
% 0.21/0.56  % (11820)------------------------------
% 0.21/0.56  % (11820)------------------------------
% 0.21/0.56  % (11796)Success in time 0.196 s
%------------------------------------------------------------------------------
