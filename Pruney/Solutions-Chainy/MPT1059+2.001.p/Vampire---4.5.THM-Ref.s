%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 185 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  357 ( 621 expanded)
%              Number of equality atoms :   67 ( 102 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f110,f114,f118,f125,f129,f134,f162,f166,f172,f195,f210,f219,f238,f265,f286,f289])).

% (14731)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (14746)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (14742)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (14743)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (14748)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (14729)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (14741)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (14748)Refutation not found, incomplete strategy% (14748)------------------------------
% (14748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14748)Termination reason: Refutation not found, incomplete strategy

% (14748)Memory used [KB]: 10618
% (14748)Time elapsed: 0.097 s
% (14748)------------------------------
% (14748)------------------------------
% (14736)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f289,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_20
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_20
    | spl5_30 ),
    inference(subsumption_resolution,[],[f287,f285])).

fof(f285,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl5_30
  <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f287,plain,
    ( k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_20 ),
    inference(resolution,[],[f282,f124])).

fof(f124,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_5
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f282,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_20 ),
    inference(superposition,[],[f177,f213])).

fof(f213,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl5_20
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f176,f105])).

fof(f105,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) )
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f174,f165])).

fof(f165,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f171,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f171,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_11
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f286,plain,
    ( ~ spl5_30
    | spl5_9
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f276,f236,f160,f284])).

fof(f160,plain,
    ( spl5_9
  <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f236,plain,
    ( spl5_24
  <=> k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f276,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | spl5_9
    | ~ spl5_24 ),
    inference(superposition,[],[f161,f237])).

fof(f237,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f236])).

fof(f161,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f265,plain,
    ( spl5_2
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | spl5_2
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f255,f86])).

fof(f86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f255,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_2
    | ~ spl5_19 ),
    inference(superposition,[],[f109,f209])).

fof(f209,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_19
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f109,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f238,plain,
    ( spl5_24
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f218,f132,f127,f116,f112,f104,f236])).

fof(f112,plain,
    ( spl5_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f116,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f127,plain,
    ( spl5_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f132,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f218,plain,
    ( k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3)
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f151,f117])).

fof(f117,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f116])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_1
    | spl5_3
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f150,f113])).

fof(f113,plain,
    ( ~ v1_xboole_0(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f150,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f149,f128])).

fof(f128,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f140,f105])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f133,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f133,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f219,plain,
    ( spl5_20
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f214,f205,f193,f212])).

fof(f193,plain,
    ( spl5_15
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f205,plain,
    ( spl5_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f214,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_15
    | ~ spl5_18 ),
    inference(superposition,[],[f206,f194])).

fof(f194,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f206,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f205])).

fof(f210,plain,
    ( spl5_18
    | spl5_19
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f144,f132,f127,f208,f205])).

fof(f144,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f138,f128])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f133,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f195,plain,
    ( spl5_15
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f135,f132,f193])).

fof(f135,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl5_7 ),
    inference(resolution,[],[f133,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f172,plain,
    ( spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f136,f132,f170])).

fof(f136,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f133,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f166,plain,
    ( spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f152,f132,f164])).

fof(f152,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f141,f75])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f141,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2)
    | ~ spl5_7 ),
    inference(resolution,[],[f133,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f162,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f54,f160])).

fof(f54,plain,(
    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

fof(f134,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f57,f132])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f129,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f56,f127])).

fof(f56,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f125,plain,
    ( spl5_5
    | spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f121,f116,f112,f123])).

fof(f121,plain,
    ( r2_hidden(sK3,sK0)
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f120,f113])).

fof(f120,plain,
    ( r2_hidden(sK3,sK0)
    | v1_xboole_0(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f117,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f118,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f53,f116])).

fof(f53,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f59,f112])).

fof(f59,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f110,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f58,f108])).

fof(f58,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f55,f104])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:09:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (14744)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (14735)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (14738)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (14728)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (14739)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (14740)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (14737)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (14734)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (14730)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (14747)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  % (14733)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (14739)Refutation not found, incomplete strategy% (14739)------------------------------
% 0.22/0.50  % (14739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (14739)Memory used [KB]: 10618
% 0.22/0.50  % (14739)Time elapsed: 0.087 s
% 0.22/0.50  % (14739)------------------------------
% 0.22/0.50  % (14739)------------------------------
% 0.22/0.50  % (14728)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (14732)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f106,f110,f114,f118,f125,f129,f134,f162,f166,f172,f195,f210,f219,f238,f265,f286,f289])).
% 0.22/0.50  % (14731)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (14746)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (14742)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (14743)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (14748)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (14729)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (14741)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (14748)Refutation not found, incomplete strategy% (14748)------------------------------
% 0.22/0.51  % (14748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14748)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (14748)Memory used [KB]: 10618
% 0.22/0.51  % (14748)Time elapsed: 0.097 s
% 0.22/0.51  % (14748)------------------------------
% 0.22/0.51  % (14748)------------------------------
% 0.22/0.51  % (14736)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    ~spl5_1 | ~spl5_5 | ~spl5_10 | ~spl5_11 | ~spl5_20 | spl5_30),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f288])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    $false | (~spl5_1 | ~spl5_5 | ~spl5_10 | ~spl5_11 | ~spl5_20 | spl5_30)),
% 0.22/0.51    inference(subsumption_resolution,[],[f287,f285])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | spl5_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f284])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    spl5_30 <=> k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    k7_partfun1(sK1,sK2,sK3) = k1_funct_1(sK2,sK3) | (~spl5_1 | ~spl5_5 | ~spl5_10 | ~spl5_11 | ~spl5_20)),
% 0.22/0.51    inference(resolution,[],[f282,f124])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    r2_hidden(sK3,sK0) | ~spl5_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f123])).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    spl5_5 <=> r2_hidden(sK3,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) ) | (~spl5_1 | ~spl5_10 | ~spl5_11 | ~spl5_20)),
% 0.22/0.51    inference(superposition,[],[f177,f213])).
% 0.22/0.51  fof(f213,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2) | ~spl5_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f212])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    spl5_20 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) ) | (~spl5_1 | ~spl5_10 | ~spl5_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f176,f105])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    v1_funct_1(sK2) | ~spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    spl5_1 <=> v1_funct_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.51  fof(f176,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) ) | (~spl5_10 | ~spl5_11)),
% 0.22/0.51    inference(subsumption_resolution,[],[f174,f165])).
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl5_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f164])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    spl5_10 <=> v1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | k1_funct_1(sK2,X0) = k7_partfun1(sK1,sK2,X0)) ) | ~spl5_11),
% 0.22/0.51    inference(resolution,[],[f171,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    v5_relat_1(sK2,sK1) | ~spl5_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f170])).
% 0.22/0.51  fof(f170,plain,(
% 0.22/0.51    spl5_11 <=> v5_relat_1(sK2,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    ~spl5_30 | spl5_9 | ~spl5_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f276,f236,f160,f284])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    spl5_9 <=> k3_funct_2(sK0,sK1,sK2,sK3) = k7_partfun1(sK1,sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    spl5_24 <=> k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.51  fof(f276,plain,(
% 0.22/0.51    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) | (spl5_9 | ~spl5_24)),
% 0.22/0.51    inference(superposition,[],[f161,f237])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3) | ~spl5_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f236])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3) | spl5_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f160])).
% 0.22/0.51  fof(f265,plain,(
% 0.22/0.51    spl5_2 | ~spl5_19),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f264])).
% 0.22/0.51  fof(f264,plain,(
% 0.22/0.51    $false | (spl5_2 | ~spl5_19)),
% 0.22/0.51    inference(subsumption_resolution,[],[f255,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_xboole_0) | (spl5_2 | ~spl5_19)),
% 0.22/0.51    inference(superposition,[],[f109,f209])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~spl5_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f208])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    spl5_19 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    ~v1_xboole_0(sK1) | spl5_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f108])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    spl5_2 <=> v1_xboole_0(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    spl5_24 | ~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f218,f132,f127,f116,f112,f104,f236])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    spl5_3 <=> v1_xboole_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    spl5_4 <=> m1_subset_1(sK3,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl5_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    spl5_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    k3_funct_2(sK0,sK1,sK2,sK3) = k1_funct_1(sK2,sK3) | (~spl5_1 | spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.22/0.51    inference(resolution,[],[f151,f117])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    m1_subset_1(sK3,sK0) | ~spl5_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f116])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | (~spl5_1 | spl5_3 | ~spl5_6 | ~spl5_7)),
% 0.22/0.51    inference(subsumption_resolution,[],[f150,f113])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0) | spl5_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f112])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | (~spl5_1 | ~spl5_6 | ~spl5_7)),
% 0.22/0.51    inference(subsumption_resolution,[],[f149,f128])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1) | ~spl5_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f127])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | (~spl5_1 | ~spl5_7)),
% 0.22/0.51    inference(subsumption_resolution,[],[f140,f105])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK1,sK2,X0) = k1_funct_1(sK2,X0)) ) | ~spl5_7),
% 0.22/0.51    inference(resolution,[],[f133,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_xboole_0(X0) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f132])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    spl5_20 | ~spl5_15 | ~spl5_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f214,f205,f193,f212])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    spl5_15 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    spl5_18 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    sK0 = k1_relat_1(sK2) | (~spl5_15 | ~spl5_18)),
% 0.22/0.51    inference(superposition,[],[f206,f194])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl5_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f193])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl5_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f205])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    spl5_18 | spl5_19 | ~spl5_6 | ~spl5_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f144,f132,f127,f208,f205])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl5_6 | ~spl5_7)),
% 0.22/0.51    inference(subsumption_resolution,[],[f138,f128])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl5_7),
% 0.22/0.51    inference(resolution,[],[f133,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    spl5_15 | ~spl5_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f135,f132,f193])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl5_7),
% 0.22/0.51    inference(resolution,[],[f133,f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    spl5_11 | ~spl5_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f136,f132,f170])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    v5_relat_1(sK2,sK1) | ~spl5_7),
% 0.22/0.51    inference(resolution,[],[f133,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f19])).
% 0.22/0.51  fof(f19,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    spl5_10 | ~spl5_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f152,f132,f164])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    v1_relat_1(sK2) | ~spl5_7),
% 0.22/0.51    inference(subsumption_resolution,[],[f141,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) | ~spl5_7),
% 0.22/0.51    inference(resolution,[],[f133,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ~spl5_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f54,f160])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    k3_funct_2(sK0,sK1,sK2,sK3) != k7_partfun1(sK1,sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k3_funct_2(X0,X1,X2,X3) != k7_partfun1(X1,X2,X3) & m1_subset_1(X3,X0)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f25])).
% 0.22/0.51  fof(f25,conjecture,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    spl5_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f57,f132])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    spl5_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f56,f127])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    spl5_5 | spl5_3 | ~spl5_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f121,f116,f112,f123])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    r2_hidden(sK3,sK0) | (spl5_3 | ~spl5_4)),
% 0.22/0.51    inference(subsumption_resolution,[],[f120,f113])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    r2_hidden(sK3,sK0) | v1_xboole_0(sK0) | ~spl5_4),
% 0.22/0.51    inference(resolution,[],[f117,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    spl5_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f53,f116])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    m1_subset_1(sK3,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ~spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f59,f112])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ~v1_xboole_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    ~spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f58,f108])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ~v1_xboole_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    spl5_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f55,f104])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    v1_funct_1(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (14728)------------------------------
% 0.22/0.51  % (14728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14728)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (14728)Memory used [KB]: 6268
% 0.22/0.51  % (14728)Time elapsed: 0.082 s
% 0.22/0.51  % (14728)------------------------------
% 0.22/0.51  % (14728)------------------------------
% 0.22/0.51  % (14727)Success in time 0.152 s
%------------------------------------------------------------------------------
