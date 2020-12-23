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
% DateTime   : Thu Dec  3 13:05:48 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 389 expanded)
%              Number of leaves         :   44 ( 163 expanded)
%              Depth                    :   14
%              Number of atoms          :  729 (1702 expanded)
%              Number of equality atoms :   99 ( 128 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f101,f106,f111,f116,f121,f126,f132,f142,f148,f162,f170,f196,f213,f223,f230,f252,f264,f289,f299,f361,f399,f429,f436,f439])).

fof(f439,plain,
    ( sK2 != k2_funct_1(sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f436,plain,
    ( ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21
    | spl3_42 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_21
    | spl3_42 ),
    inference(unit_resulting_resolution,[],[f147,f161,f212,f428,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f428,plain,
    ( sK0 != k2_relat_1(sK1)
    | spl3_42 ),
    inference(avatar_component_clause,[],[f426])).

fof(f426,plain,
    ( spl3_42
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f212,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_21
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f161,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_15
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f147,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_13
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

% (20368)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (20367)Refutation not found, incomplete strategy% (20367)------------------------------
% (20367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20367)Termination reason: Refutation not found, incomplete strategy

% (20367)Memory used [KB]: 10874
% (20367)Time elapsed: 0.157 s
% (20367)------------------------------
% (20367)------------------------------
% (20345)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (20352)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% (20365)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f429,plain,
    ( spl3_41
    | ~ spl3_42
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f420,f358,f294,f284,f193,f145,f139,f123,f103,f426,f422])).

fof(f422,plain,
    ( spl3_41
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f103,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f123,plain,
    ( spl3_10
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f139,plain,
    ( spl3_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f193,plain,
    ( spl3_19
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f284,plain,
    ( spl3_27
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f294,plain,
    ( spl3_28
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f358,plain,
    ( spl3_38
  <=> k6_relat_1(sK0) = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f420,plain,
    ( sK0 != k2_relat_1(sK1)
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f419,f286])).

fof(f286,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f284])).

fof(f419,plain,
    ( sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_28
    | ~ spl3_38 ),
    inference(trivial_inequality_removal,[],[f418])).

fof(f418,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_28
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f417,f296])).

fof(f296,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f294])).

fof(f417,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f416,f147])).

fof(f416,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_12
    | ~ spl3_19
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f415,f125])).

fof(f125,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f415,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_19
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f414,f141])).

fof(f141,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f414,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_6
    | ~ spl3_19
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f413,f105])).

fof(f105,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f413,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_19
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f410,f195])).

fof(f195,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f193])).

fof(f410,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1))
    | sK2 = k2_funct_1(sK1)
    | k2_relat_1(sK1) != k1_relat_1(sK2)
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_38 ),
    inference(superposition,[],[f69,f360])).

fof(f360,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f358])).

% (20349)Refutation not found, incomplete strategy% (20349)------------------------------
% (20349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f69,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

% (20349)Termination reason: Refutation not found, incomplete strategy

% (20349)Memory used [KB]: 10874
% (20349)Time elapsed: 0.135 s
% (20349)------------------------------
% (20349)------------------------------
fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f399,plain,
    ( ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | spl3_37 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | spl3_37 ),
    inference(unit_resulting_resolution,[],[f125,f105,f110,f90,f356,f274])).

fof(f274,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f61,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f356,plain,
    ( ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl3_37
  <=> m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f90,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f110,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f361,plain,
    ( ~ spl3_37
    | spl3_38
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f350,f261,f358,f354])).

fof(f261,plain,
    ( spl3_26
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f350,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK1,sK2)
    | ~ m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_26 ),
    inference(resolution,[],[f233,f263])).

fof(f263,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f261])).

fof(f233,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f56,f133])).

fof(f133,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f58,f59])).

fof(f59,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f299,plain,
    ( spl3_28
    | ~ spl3_7
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f298,f227,f108,f294])).

fof(f227,plain,
    ( spl3_23
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f298,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl3_7
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f291,f110])).

fof(f291,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_23 ),
    inference(superposition,[],[f70,f229])).

fof(f229,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f289,plain,
    ( spl3_27
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f288,f220,f88,f284])).

fof(f220,plain,
    ( spl3_22
  <=> sK0 = k1_relset_1(sK0,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f288,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(subsumption_resolution,[],[f281,f90])).

fof(f281,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_22 ),
    inference(superposition,[],[f70,f222])).

fof(f222,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f264,plain,
    ( spl3_26
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f259,f129,f123,f108,f103,f88,f261])).

fof(f129,plain,
    ( spl3_11
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f259,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f258,f125])).

fof(f258,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f257,f110])).

fof(f257,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f256,f105])).

fof(f256,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f253,f90])).

fof(f253,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f131,f62])).

fof(f131,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f252,plain,
    ( spl3_25
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f247,f123,f118,f113,f108,f249])).

fof(f249,plain,
    ( spl3_25
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f113,plain,
    ( spl3_8
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f118,plain,
    ( spl3_9
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f247,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f246,f125])).

fof(f246,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f245,f120])).

fof(f120,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f245,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f235,f115])).

fof(f115,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f235,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f55,f110])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f230,plain,
    ( spl3_23
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f225,f123,f118,f108,f227])).

fof(f225,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f224,f125])).

fof(f224,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f215,f120])).

fof(f215,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f68,f110])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f223,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f218,f103,f98,f88,f220])).

fof(f98,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f218,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f217,f105])).

fof(f217,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f214,f100])).

fof(f100,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f214,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK2)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f68,f90])).

fof(f213,plain,
    ( spl3_21
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f208,f123,f113,f108,f210])).

fof(f208,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f207,f125])).

fof(f207,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f198,f115])).

fof(f198,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f67,f110])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f196,plain,
    ( spl3_19
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f191,f123,f113,f108,f193])).

fof(f191,plain,
    ( v2_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f190,f125])).

fof(f190,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f181,f115])).

fof(f181,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f66,f110])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f170,plain,
    ( spl3_16
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f163,f88,f167])).

fof(f167,plain,
    ( spl3_16
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f163,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f76,f90])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f162,plain,
    ( spl3_15
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f151,f108,f159])).

fof(f151,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f73,f110])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f148,plain,
    ( spl3_13
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f143,f108,f145])).

fof(f143,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f135,f64])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f135,plain,
    ( v1_relat_1(sK1)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f63,f110])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f142,plain,
    ( spl3_12
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f137,f88,f139])).

fof(f137,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f134,f64])).

fof(f134,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f63,f90])).

fof(f132,plain,
    ( spl3_11
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f127,f83,f129])).

fof(f83,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f127,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f85,f59])).

fof(f85,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f126,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f45,f123])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f121,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f46,f118])).

fof(f46,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f116,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f47,f113])).

fof(f47,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f111,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f48,f108])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f106,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f49,f103])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f98])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f88])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f53,f83])).

fof(f53,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f78])).

fof(f78,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:40:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (20363)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (20341)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (20350)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.52  % (20342)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.23/0.53  % (20347)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.23/0.53  % (20364)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.23/0.53  % (20366)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.23/0.53  % (20344)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.53  % (20340)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.54  % (20355)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.54  % (20357)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.54  % (20339)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.54  % (20355)Refutation not found, incomplete strategy% (20355)------------------------------
% 1.34/0.54  % (20355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (20355)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (20355)Memory used [KB]: 10746
% 1.34/0.54  % (20355)Time elapsed: 0.118 s
% 1.34/0.54  % (20355)------------------------------
% 1.34/0.54  % (20355)------------------------------
% 1.34/0.54  % (20367)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (20343)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.54  % (20362)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.55  % (20361)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.55  % (20353)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.55  % (20360)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.55  % (20351)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.55  % (20354)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.55  % (20356)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.56  % (20358)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.56  % (20359)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.56  % (20349)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.56  % (20346)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.56  % (20348)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.56  % (20360)Refutation found. Thanks to Tanya!
% 1.34/0.56  % SZS status Theorem for theBenchmark
% 1.34/0.56  % SZS output start Proof for theBenchmark
% 1.34/0.56  fof(f440,plain,(
% 1.34/0.56    $false),
% 1.34/0.56    inference(avatar_sat_refutation,[],[f81,f86,f91,f101,f106,f111,f116,f121,f126,f132,f142,f148,f162,f170,f196,f213,f223,f230,f252,f264,f289,f299,f361,f399,f429,f436,f439])).
% 1.34/0.56  fof(f439,plain,(
% 1.34/0.56    sK2 != k2_funct_1(sK1) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.34/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.34/0.56  fof(f436,plain,(
% 1.34/0.56    ~spl3_13 | ~spl3_15 | ~spl3_21 | spl3_42),
% 1.34/0.56    inference(avatar_contradiction_clause,[],[f434])).
% 1.34/0.56  fof(f434,plain,(
% 1.34/0.56    $false | (~spl3_13 | ~spl3_15 | ~spl3_21 | spl3_42)),
% 1.34/0.56    inference(unit_resulting_resolution,[],[f147,f161,f212,f428,f71])).
% 1.34/0.56  fof(f71,plain,(
% 1.34/0.56    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.34/0.56    inference(cnf_transformation,[],[f44])).
% 1.34/0.56  fof(f44,plain,(
% 1.34/0.56    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.56    inference(nnf_transformation,[],[f38])).
% 1.34/0.56  fof(f38,plain,(
% 1.34/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.34/0.56    inference(flattening,[],[f37])).
% 1.34/0.56  fof(f37,plain,(
% 1.34/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.34/0.56    inference(ennf_transformation,[],[f8])).
% 1.34/0.56  fof(f8,axiom,(
% 1.34/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.34/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.34/0.56  fof(f428,plain,(
% 1.34/0.56    sK0 != k2_relat_1(sK1) | spl3_42),
% 1.34/0.56    inference(avatar_component_clause,[],[f426])).
% 1.34/0.56  fof(f426,plain,(
% 1.34/0.56    spl3_42 <=> sK0 = k2_relat_1(sK1)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.34/0.56  fof(f212,plain,(
% 1.34/0.56    v2_funct_2(sK1,sK0) | ~spl3_21),
% 1.34/0.56    inference(avatar_component_clause,[],[f210])).
% 1.34/0.56  fof(f210,plain,(
% 1.34/0.56    spl3_21 <=> v2_funct_2(sK1,sK0)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.34/0.56  fof(f161,plain,(
% 1.34/0.56    v5_relat_1(sK1,sK0) | ~spl3_15),
% 1.34/0.56    inference(avatar_component_clause,[],[f159])).
% 1.34/0.56  fof(f159,plain,(
% 1.34/0.56    spl3_15 <=> v5_relat_1(sK1,sK0)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.34/0.56  fof(f147,plain,(
% 1.34/0.56    v1_relat_1(sK1) | ~spl3_13),
% 1.34/0.56    inference(avatar_component_clause,[],[f145])).
% 1.34/0.56  fof(f145,plain,(
% 1.34/0.56    spl3_13 <=> v1_relat_1(sK1)),
% 1.34/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.34/0.56  % (20368)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.56  % (20367)Refutation not found, incomplete strategy% (20367)------------------------------
% 1.34/0.56  % (20367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (20367)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (20367)Memory used [KB]: 10874
% 1.34/0.56  % (20367)Time elapsed: 0.157 s
% 1.34/0.56  % (20367)------------------------------
% 1.34/0.56  % (20367)------------------------------
% 1.34/0.57  % (20345)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.57  % (20352)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.34/0.57  % (20365)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.58  fof(f429,plain,(
% 1.34/0.58    spl3_41 | ~spl3_42 | ~spl3_6 | ~spl3_10 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_27 | ~spl3_28 | ~spl3_38),
% 1.34/0.58    inference(avatar_split_clause,[],[f420,f358,f294,f284,f193,f145,f139,f123,f103,f426,f422])).
% 1.34/0.58  fof(f422,plain,(
% 1.34/0.58    spl3_41 <=> sK2 = k2_funct_1(sK1)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.34/0.58  fof(f103,plain,(
% 1.34/0.58    spl3_6 <=> v1_funct_1(sK2)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.34/0.58  fof(f123,plain,(
% 1.34/0.58    spl3_10 <=> v1_funct_1(sK1)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.34/0.58  fof(f139,plain,(
% 1.34/0.58    spl3_12 <=> v1_relat_1(sK2)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.34/0.58  fof(f193,plain,(
% 1.34/0.58    spl3_19 <=> v2_funct_1(sK1)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.34/0.58  fof(f284,plain,(
% 1.34/0.58    spl3_27 <=> sK0 = k1_relat_1(sK2)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.34/0.58  fof(f294,plain,(
% 1.34/0.58    spl3_28 <=> sK0 = k1_relat_1(sK1)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.34/0.58  fof(f358,plain,(
% 1.34/0.58    spl3_38 <=> k6_relat_1(sK0) = k5_relat_1(sK1,sK2)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 1.34/0.58  fof(f420,plain,(
% 1.34/0.58    sK0 != k2_relat_1(sK1) | sK2 = k2_funct_1(sK1) | (~spl3_6 | ~spl3_10 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_27 | ~spl3_28 | ~spl3_38)),
% 1.34/0.58    inference(forward_demodulation,[],[f419,f286])).
% 1.34/0.58  fof(f286,plain,(
% 1.34/0.58    sK0 = k1_relat_1(sK2) | ~spl3_27),
% 1.34/0.58    inference(avatar_component_clause,[],[f284])).
% 1.34/0.58  fof(f419,plain,(
% 1.34/0.58    sK2 = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(sK2) | (~spl3_6 | ~spl3_10 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_28 | ~spl3_38)),
% 1.34/0.58    inference(trivial_inequality_removal,[],[f418])).
% 1.34/0.58  fof(f418,plain,(
% 1.34/0.58    k6_relat_1(sK0) != k6_relat_1(sK0) | sK2 = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(sK2) | (~spl3_6 | ~spl3_10 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_28 | ~spl3_38)),
% 1.34/0.58    inference(forward_demodulation,[],[f417,f296])).
% 1.34/0.58  fof(f296,plain,(
% 1.34/0.58    sK0 = k1_relat_1(sK1) | ~spl3_28),
% 1.34/0.58    inference(avatar_component_clause,[],[f294])).
% 1.34/0.58  fof(f417,plain,(
% 1.34/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1)) | sK2 = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(sK2) | (~spl3_6 | ~spl3_10 | ~spl3_12 | ~spl3_13 | ~spl3_19 | ~spl3_38)),
% 1.34/0.58    inference(subsumption_resolution,[],[f416,f147])).
% 1.34/0.58  fof(f416,plain,(
% 1.34/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1)) | sK2 = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(sK2) | ~v1_relat_1(sK1) | (~spl3_6 | ~spl3_10 | ~spl3_12 | ~spl3_19 | ~spl3_38)),
% 1.34/0.58    inference(subsumption_resolution,[],[f415,f125])).
% 1.34/0.58  fof(f125,plain,(
% 1.34/0.58    v1_funct_1(sK1) | ~spl3_10),
% 1.34/0.58    inference(avatar_component_clause,[],[f123])).
% 1.34/0.58  fof(f415,plain,(
% 1.34/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1)) | sK2 = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_6 | ~spl3_12 | ~spl3_19 | ~spl3_38)),
% 1.34/0.58    inference(subsumption_resolution,[],[f414,f141])).
% 1.34/0.58  fof(f141,plain,(
% 1.34/0.58    v1_relat_1(sK2) | ~spl3_12),
% 1.34/0.58    inference(avatar_component_clause,[],[f139])).
% 1.34/0.58  fof(f414,plain,(
% 1.34/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1)) | sK2 = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_6 | ~spl3_19 | ~spl3_38)),
% 1.34/0.58    inference(subsumption_resolution,[],[f413,f105])).
% 1.34/0.58  fof(f105,plain,(
% 1.34/0.58    v1_funct_1(sK2) | ~spl3_6),
% 1.34/0.58    inference(avatar_component_clause,[],[f103])).
% 1.34/0.58  fof(f413,plain,(
% 1.34/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1)) | sK2 = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (~spl3_19 | ~spl3_38)),
% 1.34/0.58    inference(subsumption_resolution,[],[f410,f195])).
% 1.34/0.58  fof(f195,plain,(
% 1.34/0.58    v2_funct_1(sK1) | ~spl3_19),
% 1.34/0.58    inference(avatar_component_clause,[],[f193])).
% 1.34/0.58  fof(f410,plain,(
% 1.34/0.58    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK1)) | sK2 = k2_funct_1(sK1) | k2_relat_1(sK1) != k1_relat_1(sK2) | ~v2_funct_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_38),
% 1.34/0.58    inference(superposition,[],[f69,f360])).
% 1.34/0.58  fof(f360,plain,(
% 1.34/0.58    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~spl3_38),
% 1.34/0.58    inference(avatar_component_clause,[],[f358])).
% 1.34/0.58  % (20349)Refutation not found, incomplete strategy% (20349)------------------------------
% 1.34/0.58  % (20349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  fof(f69,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f35])).
% 1.34/0.58  % (20349)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.58  
% 1.34/0.58  % (20349)Memory used [KB]: 10874
% 1.34/0.58  % (20349)Time elapsed: 0.135 s
% 1.34/0.58  % (20349)------------------------------
% 1.34/0.58  % (20349)------------------------------
% 1.34/0.58  fof(f35,plain,(
% 1.34/0.58    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.58    inference(flattening,[],[f34])).
% 1.34/0.58  fof(f34,plain,(
% 1.34/0.58    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.34/0.58    inference(ennf_transformation,[],[f3])).
% 1.34/0.58  fof(f3,axiom,(
% 1.34/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 1.34/0.58  fof(f399,plain,(
% 1.34/0.58    ~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_10 | spl3_37),
% 1.34/0.58    inference(avatar_contradiction_clause,[],[f386])).
% 1.34/0.58  fof(f386,plain,(
% 1.34/0.58    $false | (~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_10 | spl3_37)),
% 1.34/0.58    inference(unit_resulting_resolution,[],[f125,f105,f110,f90,f356,f274])).
% 1.34/0.58  fof(f274,plain,(
% 1.34/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.34/0.58    inference(duplicate_literal_removal,[],[f273])).
% 1.34/0.58  fof(f273,plain,(
% 1.34/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.34/0.58    inference(superposition,[],[f61,f62])).
% 1.34/0.58  fof(f62,plain,(
% 1.34/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f28])).
% 1.34/0.58  fof(f28,plain,(
% 1.34/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.34/0.58    inference(flattening,[],[f27])).
% 1.34/0.58  fof(f27,plain,(
% 1.34/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.34/0.58    inference(ennf_transformation,[],[f11])).
% 1.34/0.58  fof(f11,axiom,(
% 1.34/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.34/0.58  fof(f61,plain,(
% 1.34/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f26])).
% 1.34/0.58  fof(f26,plain,(
% 1.34/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.34/0.58    inference(flattening,[],[f25])).
% 1.34/0.58  fof(f25,plain,(
% 1.34/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.34/0.58    inference(ennf_transformation,[],[f9])).
% 1.34/0.58  fof(f9,axiom,(
% 1.34/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.34/0.58  fof(f356,plain,(
% 1.34/0.58    ~m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_37),
% 1.34/0.58    inference(avatar_component_clause,[],[f354])).
% 1.34/0.58  fof(f354,plain,(
% 1.34/0.58    spl3_37 <=> m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.34/0.58  fof(f90,plain,(
% 1.34/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_3),
% 1.34/0.58    inference(avatar_component_clause,[],[f88])).
% 1.34/0.58  fof(f88,plain,(
% 1.34/0.58    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.34/0.58  fof(f110,plain,(
% 1.34/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_7),
% 1.34/0.58    inference(avatar_component_clause,[],[f108])).
% 1.34/0.58  fof(f108,plain,(
% 1.34/0.58    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.34/0.58  fof(f361,plain,(
% 1.34/0.58    ~spl3_37 | spl3_38 | ~spl3_26),
% 1.34/0.58    inference(avatar_split_clause,[],[f350,f261,f358,f354])).
% 1.34/0.58  fof(f261,plain,(
% 1.34/0.58    spl3_26 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0))),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.34/0.58  fof(f350,plain,(
% 1.34/0.58    k6_relat_1(sK0) = k5_relat_1(sK1,sK2) | ~m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_26),
% 1.34/0.58    inference(resolution,[],[f233,f263])).
% 1.34/0.58  fof(f263,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) | ~spl3_26),
% 1.34/0.58    inference(avatar_component_clause,[],[f261])).
% 1.34/0.58  fof(f233,plain,(
% 1.34/0.58    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.34/0.58    inference(resolution,[],[f56,f133])).
% 1.34/0.58  fof(f133,plain,(
% 1.34/0.58    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.34/0.58    inference(forward_demodulation,[],[f58,f59])).
% 1.34/0.58  fof(f59,plain,(
% 1.34/0.58    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f13])).
% 1.34/0.58  fof(f13,axiom,(
% 1.34/0.58    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.34/0.58  fof(f58,plain,(
% 1.34/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f17])).
% 1.34/0.58  fof(f17,plain,(
% 1.34/0.58    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.34/0.58    inference(pure_predicate_removal,[],[f10])).
% 1.34/0.58  fof(f10,axiom,(
% 1.34/0.58    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.34/0.58  fof(f56,plain,(
% 1.34/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f43])).
% 1.34/0.58  fof(f43,plain,(
% 1.34/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.58    inference(nnf_transformation,[],[f24])).
% 1.34/0.58  fof(f24,plain,(
% 1.34/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.58    inference(flattening,[],[f23])).
% 1.34/0.58  fof(f23,plain,(
% 1.34/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.34/0.58    inference(ennf_transformation,[],[f6])).
% 1.34/0.58  fof(f6,axiom,(
% 1.34/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.34/0.58  fof(f299,plain,(
% 1.34/0.58    spl3_28 | ~spl3_7 | ~spl3_23),
% 1.34/0.58    inference(avatar_split_clause,[],[f298,f227,f108,f294])).
% 1.34/0.58  fof(f227,plain,(
% 1.34/0.58    spl3_23 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.34/0.58  fof(f298,plain,(
% 1.34/0.58    sK0 = k1_relat_1(sK1) | (~spl3_7 | ~spl3_23)),
% 1.34/0.58    inference(subsumption_resolution,[],[f291,f110])).
% 1.34/0.58  fof(f291,plain,(
% 1.34/0.58    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_23),
% 1.34/0.58    inference(superposition,[],[f70,f229])).
% 1.34/0.58  fof(f229,plain,(
% 1.34/0.58    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl3_23),
% 1.34/0.58    inference(avatar_component_clause,[],[f227])).
% 1.34/0.58  fof(f70,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f36])).
% 1.34/0.58  fof(f36,plain,(
% 1.34/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.58    inference(ennf_transformation,[],[f5])).
% 1.34/0.58  fof(f5,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.34/0.58  fof(f289,plain,(
% 1.34/0.58    spl3_27 | ~spl3_3 | ~spl3_22),
% 1.34/0.58    inference(avatar_split_clause,[],[f288,f220,f88,f284])).
% 1.34/0.58  fof(f220,plain,(
% 1.34/0.58    spl3_22 <=> sK0 = k1_relset_1(sK0,sK0,sK2)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.34/0.58  fof(f288,plain,(
% 1.34/0.58    sK0 = k1_relat_1(sK2) | (~spl3_3 | ~spl3_22)),
% 1.34/0.58    inference(subsumption_resolution,[],[f281,f90])).
% 1.34/0.58  fof(f281,plain,(
% 1.34/0.58    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_22),
% 1.34/0.58    inference(superposition,[],[f70,f222])).
% 1.34/0.58  fof(f222,plain,(
% 1.34/0.58    sK0 = k1_relset_1(sK0,sK0,sK2) | ~spl3_22),
% 1.34/0.58    inference(avatar_component_clause,[],[f220])).
% 1.34/0.58  fof(f264,plain,(
% 1.34/0.58    spl3_26 | ~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11),
% 1.34/0.58    inference(avatar_split_clause,[],[f259,f129,f123,f108,f103,f88,f261])).
% 1.34/0.58  fof(f129,plain,(
% 1.34/0.58    spl3_11 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.34/0.58  fof(f259,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) | (~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_11)),
% 1.34/0.58    inference(subsumption_resolution,[],[f258,f125])).
% 1.34/0.58  fof(f258,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_11)),
% 1.34/0.58    inference(subsumption_resolution,[],[f257,f110])).
% 1.34/0.58  fof(f257,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_6 | ~spl3_11)),
% 1.34/0.58    inference(subsumption_resolution,[],[f256,f105])).
% 1.34/0.58  fof(f256,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_11)),
% 1.34/0.58    inference(subsumption_resolution,[],[f253,f90])).
% 1.34/0.58  fof(f253,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl3_11),
% 1.34/0.58    inference(superposition,[],[f131,f62])).
% 1.34/0.58  fof(f131,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | ~spl3_11),
% 1.34/0.58    inference(avatar_component_clause,[],[f129])).
% 1.34/0.58  fof(f252,plain,(
% 1.34/0.58    spl3_25 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_10),
% 1.34/0.58    inference(avatar_split_clause,[],[f247,f123,f118,f113,f108,f249])).
% 1.34/0.58  fof(f249,plain,(
% 1.34/0.58    spl3_25 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.34/0.58  fof(f113,plain,(
% 1.34/0.58    spl3_8 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.34/0.58  fof(f118,plain,(
% 1.34/0.58    spl3_9 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.34/0.58  fof(f247,plain,(
% 1.34/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_10)),
% 1.34/0.58    inference(subsumption_resolution,[],[f246,f125])).
% 1.34/0.58  fof(f246,plain,(
% 1.34/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 1.34/0.58    inference(subsumption_resolution,[],[f245,f120])).
% 1.34/0.58  fof(f120,plain,(
% 1.34/0.58    v1_funct_2(sK1,sK0,sK0) | ~spl3_9),
% 1.34/0.58    inference(avatar_component_clause,[],[f118])).
% 1.34/0.58  fof(f245,plain,(
% 1.34/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_7 | ~spl3_8)),
% 1.34/0.58    inference(subsumption_resolution,[],[f235,f115])).
% 1.34/0.58  fof(f115,plain,(
% 1.34/0.58    v3_funct_2(sK1,sK0,sK0) | ~spl3_8),
% 1.34/0.58    inference(avatar_component_clause,[],[f113])).
% 1.34/0.58  fof(f235,plain,(
% 1.34/0.58    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_7),
% 1.34/0.58    inference(resolution,[],[f55,f110])).
% 1.34/0.58  fof(f55,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f22])).
% 1.34/0.58  fof(f22,plain,(
% 1.34/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.34/0.58    inference(flattening,[],[f21])).
% 1.34/0.58  fof(f21,plain,(
% 1.34/0.58    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.34/0.58    inference(ennf_transformation,[],[f12])).
% 1.34/0.58  fof(f12,axiom,(
% 1.34/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.34/0.58  fof(f230,plain,(
% 1.34/0.58    spl3_23 | ~spl3_7 | ~spl3_9 | ~spl3_10),
% 1.34/0.58    inference(avatar_split_clause,[],[f225,f123,f118,f108,f227])).
% 1.34/0.58  fof(f225,plain,(
% 1.34/0.58    sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl3_7 | ~spl3_9 | ~spl3_10)),
% 1.34/0.58    inference(subsumption_resolution,[],[f224,f125])).
% 1.34/0.58  fof(f224,plain,(
% 1.34/0.58    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_1(sK1) | (~spl3_7 | ~spl3_9)),
% 1.34/0.58    inference(subsumption_resolution,[],[f215,f120])).
% 1.34/0.58  fof(f215,plain,(
% 1.34/0.58    sK0 = k1_relset_1(sK0,sK0,sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_7),
% 1.34/0.58    inference(resolution,[],[f68,f110])).
% 1.34/0.58  fof(f68,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0 | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f33])).
% 1.34/0.58  fof(f33,plain,(
% 1.34/0.58    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.34/0.58    inference(flattening,[],[f32])).
% 1.34/0.58  fof(f32,plain,(
% 1.34/0.58    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.34/0.58    inference(ennf_transformation,[],[f14])).
% 1.34/0.58  fof(f14,axiom,(
% 1.34/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 1.34/0.58  fof(f223,plain,(
% 1.34/0.58    spl3_22 | ~spl3_3 | ~spl3_5 | ~spl3_6),
% 1.34/0.58    inference(avatar_split_clause,[],[f218,f103,f98,f88,f220])).
% 1.34/0.58  fof(f98,plain,(
% 1.34/0.58    spl3_5 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.34/0.58  fof(f218,plain,(
% 1.34/0.58    sK0 = k1_relset_1(sK0,sK0,sK2) | (~spl3_3 | ~spl3_5 | ~spl3_6)),
% 1.34/0.58    inference(subsumption_resolution,[],[f217,f105])).
% 1.34/0.58  fof(f217,plain,(
% 1.34/0.58    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_5)),
% 1.34/0.58    inference(subsumption_resolution,[],[f214,f100])).
% 1.34/0.58  fof(f100,plain,(
% 1.34/0.58    v1_funct_2(sK2,sK0,sK0) | ~spl3_5),
% 1.34/0.58    inference(avatar_component_clause,[],[f98])).
% 1.34/0.58  fof(f214,plain,(
% 1.34/0.58    sK0 = k1_relset_1(sK0,sK0,sK2) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~spl3_3),
% 1.34/0.58    inference(resolution,[],[f68,f90])).
% 1.34/0.58  fof(f213,plain,(
% 1.34/0.58    spl3_21 | ~spl3_7 | ~spl3_8 | ~spl3_10),
% 1.34/0.58    inference(avatar_split_clause,[],[f208,f123,f113,f108,f210])).
% 1.34/0.58  fof(f208,plain,(
% 1.34/0.58    v2_funct_2(sK1,sK0) | (~spl3_7 | ~spl3_8 | ~spl3_10)),
% 1.34/0.58    inference(subsumption_resolution,[],[f207,f125])).
% 1.34/0.58  fof(f207,plain,(
% 1.34/0.58    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0) | (~spl3_7 | ~spl3_8)),
% 1.34/0.58    inference(subsumption_resolution,[],[f198,f115])).
% 1.34/0.58  fof(f198,plain,(
% 1.34/0.58    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0) | ~spl3_7),
% 1.34/0.58    inference(resolution,[],[f67,f110])).
% 1.34/0.58  fof(f67,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f31])).
% 1.34/0.58  fof(f31,plain,(
% 1.34/0.58    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.58    inference(flattening,[],[f30])).
% 1.34/0.58  fof(f30,plain,(
% 1.34/0.58    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.58    inference(ennf_transformation,[],[f7])).
% 1.34/0.58  fof(f7,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.34/0.58  fof(f196,plain,(
% 1.34/0.58    spl3_19 | ~spl3_7 | ~spl3_8 | ~spl3_10),
% 1.34/0.58    inference(avatar_split_clause,[],[f191,f123,f113,f108,f193])).
% 1.34/0.58  fof(f191,plain,(
% 1.34/0.58    v2_funct_1(sK1) | (~spl3_7 | ~spl3_8 | ~spl3_10)),
% 1.34/0.58    inference(subsumption_resolution,[],[f190,f125])).
% 1.34/0.58  fof(f190,plain,(
% 1.34/0.58    ~v1_funct_1(sK1) | v2_funct_1(sK1) | (~spl3_7 | ~spl3_8)),
% 1.34/0.58    inference(subsumption_resolution,[],[f181,f115])).
% 1.34/0.58  fof(f181,plain,(
% 1.34/0.58    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_1(sK1) | ~spl3_7),
% 1.34/0.58    inference(resolution,[],[f66,f110])).
% 1.34/0.58  fof(f66,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_1(X2)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f31])).
% 1.34/0.58  fof(f170,plain,(
% 1.34/0.58    spl3_16 | ~spl3_3),
% 1.34/0.58    inference(avatar_split_clause,[],[f163,f88,f167])).
% 1.34/0.58  fof(f167,plain,(
% 1.34/0.58    spl3_16 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.34/0.58  fof(f163,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_3),
% 1.34/0.58    inference(resolution,[],[f76,f90])).
% 1.34/0.58  fof(f76,plain,(
% 1.34/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.34/0.58    inference(duplicate_literal_removal,[],[f74])).
% 1.34/0.58  fof(f74,plain,(
% 1.34/0.58    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.58    inference(equality_resolution,[],[f57])).
% 1.34/0.58  fof(f57,plain,(
% 1.34/0.58    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f43])).
% 1.34/0.58  fof(f162,plain,(
% 1.34/0.58    spl3_15 | ~spl3_7),
% 1.34/0.58    inference(avatar_split_clause,[],[f151,f108,f159])).
% 1.34/0.58  fof(f151,plain,(
% 1.34/0.58    v5_relat_1(sK1,sK0) | ~spl3_7),
% 1.34/0.58    inference(resolution,[],[f73,f110])).
% 1.34/0.58  fof(f73,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f39])).
% 1.34/0.58  fof(f39,plain,(
% 1.34/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.34/0.58    inference(ennf_transformation,[],[f18])).
% 1.34/0.58  fof(f18,plain,(
% 1.34/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.34/0.58    inference(pure_predicate_removal,[],[f4])).
% 1.34/0.58  fof(f4,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.34/0.58  fof(f148,plain,(
% 1.34/0.58    spl3_13 | ~spl3_7),
% 1.34/0.58    inference(avatar_split_clause,[],[f143,f108,f145])).
% 1.34/0.58  fof(f143,plain,(
% 1.34/0.58    v1_relat_1(sK1) | ~spl3_7),
% 1.34/0.58    inference(subsumption_resolution,[],[f135,f64])).
% 1.34/0.58  fof(f64,plain,(
% 1.34/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f2])).
% 1.34/0.58  fof(f2,axiom,(
% 1.34/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.34/0.58  fof(f135,plain,(
% 1.34/0.58    v1_relat_1(sK1) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | ~spl3_7),
% 1.34/0.58    inference(resolution,[],[f63,f110])).
% 1.34/0.58  fof(f63,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f29])).
% 1.34/0.58  fof(f29,plain,(
% 1.34/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.34/0.58    inference(ennf_transformation,[],[f1])).
% 1.34/0.58  fof(f1,axiom,(
% 1.34/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.34/0.58  fof(f142,plain,(
% 1.34/0.58    spl3_12 | ~spl3_3),
% 1.34/0.58    inference(avatar_split_clause,[],[f137,f88,f139])).
% 1.34/0.58  fof(f137,plain,(
% 1.34/0.58    v1_relat_1(sK2) | ~spl3_3),
% 1.34/0.58    inference(subsumption_resolution,[],[f134,f64])).
% 1.34/0.58  fof(f134,plain,(
% 1.34/0.58    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | ~spl3_3),
% 1.34/0.58    inference(resolution,[],[f63,f90])).
% 1.34/0.58  fof(f132,plain,(
% 1.34/0.58    spl3_11 | ~spl3_2),
% 1.34/0.58    inference(avatar_split_clause,[],[f127,f83,f129])).
% 1.34/0.58  fof(f83,plain,(
% 1.34/0.58    spl3_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.34/0.58  fof(f127,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | ~spl3_2),
% 1.34/0.58    inference(backward_demodulation,[],[f85,f59])).
% 1.34/0.58  fof(f85,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) | ~spl3_2),
% 1.34/0.58    inference(avatar_component_clause,[],[f83])).
% 1.34/0.58  fof(f126,plain,(
% 1.34/0.58    spl3_10),
% 1.34/0.58    inference(avatar_split_clause,[],[f45,f123])).
% 1.34/0.58  fof(f45,plain,(
% 1.34/0.58    v1_funct_1(sK1)),
% 1.34/0.58    inference(cnf_transformation,[],[f42])).
% 1.34/0.58  fof(f42,plain,(
% 1.34/0.58    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.34/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f41,f40])).
% 1.34/0.58  fof(f40,plain,(
% 1.34/0.58    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.34/0.58    introduced(choice_axiom,[])).
% 1.34/0.58  fof(f41,plain,(
% 1.34/0.58    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.34/0.58    introduced(choice_axiom,[])).
% 1.34/0.58  fof(f20,plain,(
% 1.34/0.58    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.34/0.58    inference(flattening,[],[f19])).
% 1.34/0.58  fof(f19,plain,(
% 1.34/0.58    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.34/0.58    inference(ennf_transformation,[],[f16])).
% 1.34/0.58  fof(f16,negated_conjecture,(
% 1.34/0.58    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.34/0.58    inference(negated_conjecture,[],[f15])).
% 1.34/0.58  fof(f15,conjecture,(
% 1.34/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 1.34/0.58  fof(f121,plain,(
% 1.34/0.58    spl3_9),
% 1.34/0.58    inference(avatar_split_clause,[],[f46,f118])).
% 1.34/0.58  fof(f46,plain,(
% 1.34/0.58    v1_funct_2(sK1,sK0,sK0)),
% 1.34/0.58    inference(cnf_transformation,[],[f42])).
% 1.34/0.58  fof(f116,plain,(
% 1.34/0.58    spl3_8),
% 1.34/0.58    inference(avatar_split_clause,[],[f47,f113])).
% 1.34/0.58  fof(f47,plain,(
% 1.34/0.58    v3_funct_2(sK1,sK0,sK0)),
% 1.34/0.58    inference(cnf_transformation,[],[f42])).
% 1.34/0.58  fof(f111,plain,(
% 1.34/0.58    spl3_7),
% 1.34/0.58    inference(avatar_split_clause,[],[f48,f108])).
% 1.34/0.58  fof(f48,plain,(
% 1.34/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.58    inference(cnf_transformation,[],[f42])).
% 1.34/0.58  fof(f106,plain,(
% 1.34/0.58    spl3_6),
% 1.34/0.58    inference(avatar_split_clause,[],[f49,f103])).
% 1.34/0.58  fof(f49,plain,(
% 1.34/0.58    v1_funct_1(sK2)),
% 1.34/0.58    inference(cnf_transformation,[],[f42])).
% 1.34/0.58  fof(f101,plain,(
% 1.34/0.58    spl3_5),
% 1.34/0.58    inference(avatar_split_clause,[],[f50,f98])).
% 1.34/0.58  fof(f50,plain,(
% 1.34/0.58    v1_funct_2(sK2,sK0,sK0)),
% 1.34/0.58    inference(cnf_transformation,[],[f42])).
% 1.34/0.58  fof(f91,plain,(
% 1.34/0.58    spl3_3),
% 1.34/0.58    inference(avatar_split_clause,[],[f52,f88])).
% 1.34/0.58  fof(f52,plain,(
% 1.34/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.34/0.58    inference(cnf_transformation,[],[f42])).
% 1.34/0.58  fof(f86,plain,(
% 1.34/0.58    spl3_2),
% 1.34/0.58    inference(avatar_split_clause,[],[f53,f83])).
% 1.34/0.58  fof(f53,plain,(
% 1.34/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.34/0.58    inference(cnf_transformation,[],[f42])).
% 1.34/0.58  fof(f81,plain,(
% 1.34/0.58    ~spl3_1),
% 1.34/0.58    inference(avatar_split_clause,[],[f54,f78])).
% 1.34/0.58  fof(f78,plain,(
% 1.34/0.58    spl3_1 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.34/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.34/0.58  fof(f54,plain,(
% 1.34/0.58    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.34/0.58    inference(cnf_transformation,[],[f42])).
% 1.34/0.58  % SZS output end Proof for theBenchmark
% 1.34/0.58  % (20360)------------------------------
% 1.34/0.58  % (20360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  % (20360)Termination reason: Refutation
% 1.34/0.58  
% 1.34/0.58  % (20360)Memory used [KB]: 6524
% 1.34/0.58  % (20360)Time elapsed: 0.121 s
% 1.34/0.58  % (20360)------------------------------
% 1.34/0.58  % (20360)------------------------------
% 1.34/0.59  % (20338)Success in time 0.221 s
%------------------------------------------------------------------------------
