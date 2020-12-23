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
% DateTime   : Thu Dec  3 13:07:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 270 expanded)
%              Number of leaves         :   34 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  519 (1044 expanded)
%              Number of equality atoms :  104 ( 198 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f91,f96,f101,f118,f129,f134,f151,f169,f180,f223,f228,f231,f236,f248,f255,f261,f270,f277,f280])).

fof(f280,plain,
    ( spl6_5
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl6_5
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f278,f81])).

fof(f81,plain,
    ( k1_xboole_0 != sK1
    | spl6_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f278,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_32 ),
    inference(resolution,[],[f276,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f276,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl6_32
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f277,plain,
    ( spl6_32
    | ~ spl6_4
    | spl6_31 ),
    inference(avatar_split_clause,[],[f272,f267,f74,f274])).

fof(f74,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f267,plain,
    ( spl6_31
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f272,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_4
    | spl6_31 ),
    inference(subsumption_resolution,[],[f271,f76])).

fof(f76,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f271,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl6_31 ),
    inference(resolution,[],[f269,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f269,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f267])).

fof(f270,plain,
    ( ~ spl6_31
    | ~ spl6_1
    | ~ spl6_24
    | ~ spl6_26
    | spl6_30 ),
    inference(avatar_split_clause,[],[f265,f258,f221,f210,f59,f267])).

fof(f59,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f210,plain,
    ( spl6_24
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f221,plain,
    ( spl6_26
  <=> ! [X5,X6] :
        ( ~ r2_hidden(X6,sK1)
        | k1_funct_1(k5_relat_1(sK3,X5),X6) = k1_funct_1(X5,k1_funct_1(sK3,X6))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f258,plain,
    ( spl6_30
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f265,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ spl6_1
    | ~ spl6_24
    | ~ spl6_26
    | spl6_30 ),
    inference(subsumption_resolution,[],[f264,f61])).

fof(f61,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f264,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ v1_funct_1(sK4)
    | ~ spl6_24
    | ~ spl6_26
    | spl6_30 ),
    inference(subsumption_resolution,[],[f263,f211])).

fof(f211,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f263,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ spl6_26
    | spl6_30 ),
    inference(trivial_inequality_removal,[],[f262])).

fof(f262,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(sK5,sK1)
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ spl6_26
    | spl6_30 ),
    inference(superposition,[],[f260,f222])).

fof(f222,plain,
    ( ! [X6,X5] :
        ( k1_funct_1(k5_relat_1(sK3,X5),X6) = k1_funct_1(X5,k1_funct_1(sK3,X6))
        | ~ r2_hidden(X6,sK1)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f221])).

fof(f260,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f258])).

fof(f261,plain,
    ( ~ spl6_30
    | spl6_12
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f256,f250,f131,f258])).

fof(f131,plain,
    ( spl6_12
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f250,plain,
    ( spl6_29
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f256,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5)
    | spl6_12
    | ~ spl6_29 ),
    inference(superposition,[],[f133,f252])).

fof(f252,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f250])).

fof(f133,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f255,plain,
    ( spl6_29
    | ~ spl6_27
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f253,f245,f233,f250])).

fof(f233,plain,
    ( spl6_27
  <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f245,plain,
    ( spl6_28
  <=> k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f253,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_27
    | ~ spl6_28 ),
    inference(superposition,[],[f247,f235])).

fof(f235,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f233])).

fof(f247,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f245])).

fof(f248,plain,
    ( spl6_28
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f242,f98,f93,f64,f59,f245])).

fof(f64,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

% (9079)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (9071)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f93,plain,
    ( spl6_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f98,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f242,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(resolution,[],[f238,f95])).

fof(f95,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f238,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,X0,X1,sK3,sK4) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(resolution,[],[f237,f61])).

fof(f237,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k5_relat_1(sK3,X0) = k1_partfun1(sK1,sK2,X1,X2,sK3,X0) )
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(resolution,[],[f85,f100])).

fof(f100,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f85,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_partfun1(X0,X1,X3,X4,sK3,X2) = k5_relat_1(sK3,X2) )
    | ~ spl6_2 ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f66,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f236,plain,
    ( spl6_27
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_14 ),
    inference(avatar_split_clause,[],[f225,f148,f115,f98,f93,f88,f64,f59,f233])).

fof(f88,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f115,plain,
    ( spl6_10
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f148,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f225,plain,
    ( k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_14 ),
    inference(subsumption_resolution,[],[f124,f149])).

% (9077)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f149,plain,
    ( k1_xboole_0 != sK2
    | spl6_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f124,plain,
    ( k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f123,f66])).

fof(f123,plain,
    ( ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f122,f95])).

fof(f122,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f121,f61])).

fof(f121,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f120,f100])).

fof(f120,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f119,f90])).

fof(f90,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f119,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2
    | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)
    | ~ spl6_10 ),
    inference(resolution,[],[f117,f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X1
      | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
          | k1_xboole_0 = X1
          | ~ r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_1(X4) )
         => ( r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))
           => ( k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)
              | k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

fof(f117,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f231,plain,
    ( ~ spl6_8
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl6_8
    | spl6_25 ),
    inference(subsumption_resolution,[],[f229,f41])).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f229,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ spl6_8
    | spl6_25 ),
    inference(resolution,[],[f224,f100])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_25 ),
    inference(resolution,[],[f219,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f219,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl6_25
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f228,plain,
    ( ~ spl6_7
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl6_7
    | spl6_24 ),
    inference(subsumption_resolution,[],[f226,f41])).

fof(f226,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | ~ spl6_7
    | spl6_24 ),
    inference(resolution,[],[f214,f95])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_24 ),
    inference(resolution,[],[f212,f40])).

fof(f212,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f223,plain,
    ( ~ spl6_25
    | spl6_26
    | ~ spl6_2
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f215,f171,f64,f221,f217])).

fof(f171,plain,
    ( spl6_17
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f215,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,sK1)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | k1_funct_1(k5_relat_1(sK3,X5),X6) = k1_funct_1(X5,k1_funct_1(sK3,X6)) )
    | ~ spl6_2
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f86,f173])).

fof(f173,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f171])).

fof(f86,plain,
    ( ! [X6,X5] :
        ( ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | ~ r2_hidden(X6,k1_relat_1(sK3))
        | k1_funct_1(k5_relat_1(sK3,X5),X6) = k1_funct_1(X5,k1_funct_1(sK3,X6)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f66,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f180,plain,
    ( spl6_17
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f174,f144,f126,f171])).

fof(f126,plain,
    ( spl6_11
  <=> k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f144,plain,
    ( spl6_13
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f174,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(superposition,[],[f146,f128])).

fof(f128,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f146,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f169,plain,
    ( spl6_3
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | spl6_3
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f160,f38])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f160,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_14 ),
    inference(superposition,[],[f71,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f71,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f151,plain,
    ( spl6_13
    | spl6_14
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f108,f98,f88,f148,f144])).

fof(f108,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f106,f90])).

fof(f106,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f134,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f31,f131])).

fof(f31,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f129,plain,
    ( spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f107,f98,f126])).

fof(f107,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_8 ),
    inference(resolution,[],[f100,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f118,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f29,f115])).

fof(f29,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f36,f98])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f96,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f33,f93])).

% (9071)Refutation not found, incomplete strategy% (9071)------------------------------
% (9071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9071)Termination reason: Refutation not found, incomplete strategy

% (9071)Memory used [KB]: 10618
% (9071)Time elapsed: 0.068 s
% (9071)------------------------------
% (9071)------------------------------
fof(f33,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f82,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f30,f79])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f37,f69])).

fof(f37,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f34,f64])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:30:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (9073)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (9081)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (9087)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (9073)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f281,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f91,f96,f101,f118,f129,f134,f151,f169,f180,f223,f228,f231,f236,f248,f255,f261,f270,f277,f280])).
% 0.22/0.48  fof(f280,plain,(
% 0.22/0.48    spl6_5 | ~spl6_32),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f279])).
% 0.22/0.48  fof(f279,plain,(
% 0.22/0.48    $false | (spl6_5 | ~spl6_32)),
% 0.22/0.48    inference(subsumption_resolution,[],[f278,f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    k1_xboole_0 != sK1 | spl6_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl6_5 <=> k1_xboole_0 = sK1),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.48  fof(f278,plain,(
% 0.22/0.48    k1_xboole_0 = sK1 | ~spl6_32),
% 0.22/0.48    inference(resolution,[],[f276,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.48  fof(f276,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | ~spl6_32),
% 0.22/0.48    inference(avatar_component_clause,[],[f274])).
% 0.22/0.48  fof(f274,plain,(
% 0.22/0.48    spl6_32 <=> v1_xboole_0(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.48  fof(f277,plain,(
% 0.22/0.48    spl6_32 | ~spl6_4 | spl6_31),
% 0.22/0.48    inference(avatar_split_clause,[],[f272,f267,f74,f274])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl6_4 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.48  fof(f267,plain,(
% 0.22/0.48    spl6_31 <=> r2_hidden(sK5,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.22/0.48  fof(f272,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | (~spl6_4 | spl6_31)),
% 0.22/0.48    inference(subsumption_resolution,[],[f271,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    m1_subset_1(sK5,sK1) | ~spl6_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f74])).
% 0.22/0.48  fof(f271,plain,(
% 0.22/0.48    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl6_31),
% 0.22/0.48    inference(resolution,[],[f269,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.48  fof(f269,plain,(
% 0.22/0.48    ~r2_hidden(sK5,sK1) | spl6_31),
% 0.22/0.48    inference(avatar_component_clause,[],[f267])).
% 0.22/0.48  fof(f270,plain,(
% 0.22/0.48    ~spl6_31 | ~spl6_1 | ~spl6_24 | ~spl6_26 | spl6_30),
% 0.22/0.48    inference(avatar_split_clause,[],[f265,f258,f221,f210,f59,f267])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl6_1 <=> v1_funct_1(sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    spl6_24 <=> v1_relat_1(sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.48  fof(f221,plain,(
% 0.22/0.48    spl6_26 <=> ! [X5,X6] : (~r2_hidden(X6,sK1) | k1_funct_1(k5_relat_1(sK3,X5),X6) = k1_funct_1(X5,k1_funct_1(sK3,X6)) | ~v1_relat_1(X5) | ~v1_funct_1(X5))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.22/0.48  fof(f258,plain,(
% 0.22/0.48    spl6_30 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k5_relat_1(sK3,sK4),sK5)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.48  fof(f265,plain,(
% 0.22/0.48    ~r2_hidden(sK5,sK1) | (~spl6_1 | ~spl6_24 | ~spl6_26 | spl6_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f264,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    v1_funct_1(sK4) | ~spl6_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f59])).
% 0.22/0.48  fof(f264,plain,(
% 0.22/0.48    ~r2_hidden(sK5,sK1) | ~v1_funct_1(sK4) | (~spl6_24 | ~spl6_26 | spl6_30)),
% 0.22/0.48    inference(subsumption_resolution,[],[f263,f211])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    v1_relat_1(sK4) | ~spl6_24),
% 0.22/0.48    inference(avatar_component_clause,[],[f210])).
% 0.22/0.48  fof(f263,plain,(
% 0.22/0.48    ~r2_hidden(sK5,sK1) | ~v1_relat_1(sK4) | ~v1_funct_1(sK4) | (~spl6_26 | spl6_30)),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f262])).
% 0.22/0.48  fof(f262,plain,(
% 0.22/0.48    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(sK5,sK1) | ~v1_relat_1(sK4) | ~v1_funct_1(sK4) | (~spl6_26 | spl6_30)),
% 0.22/0.48    inference(superposition,[],[f260,f222])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    ( ! [X6,X5] : (k1_funct_1(k5_relat_1(sK3,X5),X6) = k1_funct_1(X5,k1_funct_1(sK3,X6)) | ~r2_hidden(X6,sK1) | ~v1_relat_1(X5) | ~v1_funct_1(X5)) ) | ~spl6_26),
% 0.22/0.48    inference(avatar_component_clause,[],[f221])).
% 0.22/0.48  fof(f260,plain,(
% 0.22/0.48    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | spl6_30),
% 0.22/0.48    inference(avatar_component_clause,[],[f258])).
% 0.22/0.48  fof(f261,plain,(
% 0.22/0.48    ~spl6_30 | spl6_12 | ~spl6_29),
% 0.22/0.48    inference(avatar_split_clause,[],[f256,f250,f131,f258])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    spl6_12 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.48  fof(f250,plain,(
% 0.22/0.48    spl6_29 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.22/0.48  fof(f256,plain,(
% 0.22/0.48    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k5_relat_1(sK3,sK4),sK5) | (spl6_12 | ~spl6_29)),
% 0.22/0.48    inference(superposition,[],[f133,f252])).
% 0.22/0.48  fof(f252,plain,(
% 0.22/0.48    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl6_29),
% 0.22/0.48    inference(avatar_component_clause,[],[f250])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_12),
% 0.22/0.48    inference(avatar_component_clause,[],[f131])).
% 0.22/0.48  fof(f255,plain,(
% 0.22/0.48    spl6_29 | ~spl6_27 | ~spl6_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f253,f245,f233,f250])).
% 0.22/0.48  fof(f233,plain,(
% 0.22/0.48    spl6_27 <=> k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.48  fof(f245,plain,(
% 0.22/0.48    spl6_28 <=> k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.48  fof(f253,plain,(
% 0.22/0.48    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl6_27 | ~spl6_28)),
% 0.22/0.48    inference(superposition,[],[f247,f235])).
% 0.22/0.48  fof(f235,plain,(
% 0.22/0.48    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~spl6_27),
% 0.22/0.48    inference(avatar_component_clause,[],[f233])).
% 0.22/0.48  fof(f247,plain,(
% 0.22/0.48    k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | ~spl6_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f245])).
% 0.22/0.48  fof(f248,plain,(
% 0.22/0.48    spl6_28 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f242,f98,f93,f64,f59,f245])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl6_2 <=> v1_funct_1(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.48  % (9079)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (9071)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    spl6_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl6_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8)),
% 0.22/0.49    inference(resolution,[],[f238,f95])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f93])).
% 0.22/0.49  fof(f238,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK3,sK4) = k1_partfun1(sK1,sK2,X0,X1,sK3,sK4)) ) | (~spl6_1 | ~spl6_2 | ~spl6_8)),
% 0.22/0.49    inference(resolution,[],[f237,f61])).
% 0.22/0.49  fof(f237,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK3,X0) = k1_partfun1(sK1,sK2,X1,X2,sK3,X0)) ) | (~spl6_2 | ~spl6_8)),
% 0.22/0.49    inference(resolution,[],[f85,f100])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f98])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X0,X1,X3,X4,sK3,X2) = k5_relat_1(sK3,X2)) ) | ~spl6_2),
% 0.22/0.49    inference(resolution,[],[f66,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.49    inference(flattening,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    v1_funct_1(sK3) | ~spl6_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    spl6_27 | ~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | spl6_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f225,f148,f115,f98,f93,f88,f64,f59,f233])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl6_6 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl6_10 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    spl6_14 <=> k1_xboole_0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | spl6_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f124,f149])).
% 0.22/0.49  % (9077)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    k1_xboole_0 != sK2 | spl6_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f148])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f123,f66])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f122,f95])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_1 | ~spl6_6 | ~spl6_8 | ~spl6_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f121,f61])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_6 | ~spl6_8 | ~spl6_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f120,f100])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | (~spl6_6 | ~spl6_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f119,f90])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    v1_funct_2(sK3,sK1,sK2) | ~spl6_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f88])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK3) | k1_xboole_0 = sK2 | k8_funct_2(sK1,sK2,sK0,sK3,sK4) = k1_partfun1(sK1,sK2,sK2,sK0,sK3,sK4) | ~spl6_10),
% 0.22/0.49    inference(resolution,[],[f117,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X1 | k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (! [X4] : (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (! [X4] : (((k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4)) => (r1_tarski(k2_relset_1(X0,X1,X3),k1_relset_1(X1,X2,X4)) => (k8_funct_2(X0,X1,X2,X3,X4) = k1_partfun1(X0,X1,X1,X2,X3,X4) | k1_xboole_0 = X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f115])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    ~spl6_8 | spl6_25),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f230])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    $false | (~spl6_8 | spl6_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f229,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | (~spl6_8 | spl6_25)),
% 0.22/0.49    inference(resolution,[],[f224,f100])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_25),
% 0.22/0.49    inference(resolution,[],[f219,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f219,plain,(
% 0.22/0.49    ~v1_relat_1(sK3) | spl6_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f217])).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    spl6_25 <=> v1_relat_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    ~spl6_7 | spl6_24),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f227])).
% 0.22/0.49  fof(f227,plain,(
% 0.22/0.49    $false | (~spl6_7 | spl6_24)),
% 0.22/0.49    inference(subsumption_resolution,[],[f226,f41])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | (~spl6_7 | spl6_24)),
% 0.22/0.49    inference(resolution,[],[f214,f95])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_24),
% 0.22/0.49    inference(resolution,[],[f212,f40])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    ~v1_relat_1(sK4) | spl6_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f210])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    ~spl6_25 | spl6_26 | ~spl6_2 | ~spl6_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f215,f171,f64,f221,f217])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    spl6_17 <=> sK1 = k1_relat_1(sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.49  fof(f215,plain,(
% 0.22/0.49    ( ! [X6,X5] : (~r2_hidden(X6,sK1) | ~v1_relat_1(sK3) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | k1_funct_1(k5_relat_1(sK3,X5),X6) = k1_funct_1(X5,k1_funct_1(sK3,X6))) ) | (~spl6_2 | ~spl6_17)),
% 0.22/0.49    inference(forward_demodulation,[],[f86,f173])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    sK1 = k1_relat_1(sK3) | ~spl6_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f171])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X6,X5] : (~v1_relat_1(sK3) | ~v1_relat_1(X5) | ~v1_funct_1(X5) | ~r2_hidden(X6,k1_relat_1(sK3)) | k1_funct_1(k5_relat_1(sK3,X5),X6) = k1_funct_1(X5,k1_funct_1(sK3,X6))) ) | ~spl6_2),
% 0.22/0.49    inference(resolution,[],[f66,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    spl6_17 | ~spl6_11 | ~spl6_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f174,f144,f126,f171])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl6_11 <=> k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    spl6_13 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    sK1 = k1_relat_1(sK3) | (~spl6_11 | ~spl6_13)),
% 0.22/0.49    inference(superposition,[],[f146,f128])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) | ~spl6_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f126])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f144])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    spl6_3 | ~spl6_14),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f168])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    $false | (spl6_3 | ~spl6_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f160,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_14)),
% 0.22/0.49    inference(superposition,[],[f71,f150])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | ~spl6_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f148])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ~v1_xboole_0(sK2) | spl6_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl6_3 <=> v1_xboole_0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    spl6_13 | spl6_14 | ~spl6_6 | ~spl6_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f108,f98,f88,f148,f144])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl6_6 | ~spl6_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f106,f90])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2) | ~spl6_8),
% 0.22/0.49    inference(resolution,[],[f100,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    ~spl6_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f131])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k1_funct_1(X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    spl6_11 | ~spl6_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f107,f98,f126])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) | ~spl6_8),
% 0.22/0.49    inference(resolution,[],[f100,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    spl6_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f115])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl6_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f98])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl6_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f93])).
% 0.22/0.49  % (9071)Refutation not found, incomplete strategy% (9071)------------------------------
% 0.22/0.49  % (9071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9071)Memory used [KB]: 10618
% 0.22/0.49  % (9071)Time elapsed: 0.068 s
% 0.22/0.49  % (9071)------------------------------
% 0.22/0.49  % (9071)------------------------------
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl6_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f88])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ~spl6_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f79])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    k1_xboole_0 != sK1),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl6_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f74])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    m1_subset_1(sK5,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ~spl6_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f69])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ~v1_xboole_0(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl6_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f64])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v1_funct_1(sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl6_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f59])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    v1_funct_1(sK4)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (9073)------------------------------
% 0.22/0.49  % (9073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9073)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (9073)Memory used [KB]: 10746
% 0.22/0.49  % (9073)Time elapsed: 0.070 s
% 0.22/0.49  % (9073)------------------------------
% 0.22/0.49  % (9073)------------------------------
% 0.22/0.49  % (9069)Success in time 0.129 s
%------------------------------------------------------------------------------
