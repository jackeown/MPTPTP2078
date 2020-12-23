%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 534 expanded)
%              Number of leaves         :   66 ( 253 expanded)
%              Depth                    :   17
%              Number of atoms          :  936 (2344 expanded)
%              Number of equality atoms :  154 ( 474 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5532)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (5525)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f1085,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f158,f170,f183,f201,f202,f233,f304,f397,f426,f437,f456,f473,f478,f497,f502,f508,f520,f532,f544,f668,f680,f698,f703,f724,f839,f848,f891,f919,f986,f1082,f1084])).

% (5524)Refutation not found, incomplete strategy% (5524)------------------------------
% (5524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5523)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f1084,plain,
    ( k1_xboole_0 != sK7
    | sK5 != sK7
    | k1_xboole_0 = sK5 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1082,plain,
    ( ~ spl10_6
    | ~ spl10_17
    | ~ spl10_21
    | ~ spl10_78
    | spl10_96 ),
    inference(avatar_contradiction_clause,[],[f1081])).

fof(f1081,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_21
    | ~ spl10_78
    | spl10_96 ),
    inference(subsumption_resolution,[],[f1079,f985])).

fof(f985,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | spl10_96 ),
    inference(avatar_component_clause,[],[f983])).

% (5535)Refutation not found, incomplete strategy% (5535)------------------------------
% (5535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5535)Termination reason: Refutation not found, incomplete strategy

% (5535)Memory used [KB]: 6140
% (5535)Time elapsed: 0.080 s
% (5535)------------------------------
% (5535)------------------------------
fof(f983,plain,
    ( spl10_96
  <=> k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f1079,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_21
    | ~ spl10_78 ),
    inference(unit_resulting_resolution,[],[f199,f231,f122,f838,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f838,plain,
    ( r2_hidden(k1_funct_1(sK7,sK9),k1_relat_1(sK8))
    | ~ spl10_78 ),
    inference(avatar_component_clause,[],[f836])).

fof(f836,plain,
    ( spl10_78
  <=> r2_hidden(k1_funct_1(sK7,sK9),k1_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f122,plain,
    ( v1_funct_1(sK8)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl10_6
  <=> v1_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f231,plain,
    ( v5_relat_1(sK8,sK4)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl10_21
  <=> v5_relat_1(sK8,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f199,plain,
    ( v1_relat_1(sK8)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl10_17
  <=> v1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f986,plain,
    ( ~ spl10_96
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | spl10_10
    | ~ spl10_39
    | ~ spl10_48
    | ~ spl10_53 ),
    inference(avatar_split_clause,[],[f981,f529,f499,f423,f140,f135,f130,f125,f120,f115,f110,f100,f95,f983])).

fof(f95,plain,
    ( spl10_1
  <=> k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f100,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f110,plain,
    ( spl10_4
  <=> m1_subset_1(sK9,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f115,plain,
    ( spl10_5
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f125,plain,
    ( spl10_7
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f130,plain,
    ( spl10_8
  <=> v1_funct_2(sK7,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f135,plain,
    ( spl10_9
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f140,plain,
    ( spl10_10
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f423,plain,
    ( spl10_39
  <=> k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f499,plain,
    ( spl10_48
  <=> k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f529,plain,
    ( spl10_53
  <=> r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f981,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | spl10_10
    | ~ spl10_39
    | ~ spl10_48
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f980,f531])).

fof(f531,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8))
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f529])).

% (5530)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f980,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8))
    | k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | spl10_10
    | ~ spl10_39
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f979,f425])).

fof(f425,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7)
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f423])).

fof(f979,plain,
    ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relat_1(sK8))
    | k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | spl10_10
    | ~ spl10_48 ),
    inference(forward_demodulation,[],[f978,f501])).

fof(f501,plain,
    ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8)
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f499])).

fof(f978,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | spl10_10 ),
    inference(subsumption_resolution,[],[f977,f142])).

fof(f142,plain,
    ( ~ v1_xboole_0(sK6)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f977,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | v1_xboole_0(sK6)
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f976,f137])).

fof(f137,plain,
    ( v1_funct_1(sK7)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f976,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f975,f132])).

fof(f132,plain,
    ( v1_funct_2(sK7,sK5,sK6)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f975,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f974,f127])).

fof(f127,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f974,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f973,f122])).

fof(f973,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f972,f117])).

fof(f117,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f972,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | spl10_1
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f971,f112])).

fof(f112,plain,
    ( m1_subset_1(sK9,sK5)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f971,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ m1_subset_1(sK9,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f970,f102])).

fof(f102,plain,
    ( k1_xboole_0 != sK5
    | spl10_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f970,plain,
    ( k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9))
    | k1_xboole_0 = sK5
    | ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ m1_subset_1(sK9,sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ v1_funct_1(sK7)
    | v1_xboole_0(sK6)
    | spl10_1 ),
    inference(superposition,[],[f97,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f12])).

% (5540)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f12,axiom,(
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

fof(f97,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f919,plain,
    ( spl10_37
    | ~ spl10_51
    | ~ spl10_77 ),
    inference(avatar_split_clause,[],[f896,f823,f517,f393])).

fof(f393,plain,
    ( spl10_37
  <=> sP0(k1_xboole_0,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f517,plain,
    ( spl10_51
  <=> sP0(k1_relat_1(sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f823,plain,
    ( spl10_77
  <=> k1_xboole_0 = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f896,plain,
    ( sP0(k1_xboole_0,sK7)
    | ~ spl10_51
    | ~ spl10_77 ),
    inference(backward_demodulation,[],[f519,f825])).

fof(f825,plain,
    ( k1_xboole_0 = k1_relat_1(sK8)
    | ~ spl10_77 ),
    inference(avatar_component_clause,[],[f823])).

fof(f519,plain,
    ( sP0(k1_relat_1(sK8),sK7)
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f517])).

fof(f891,plain,
    ( spl10_86
    | ~ spl10_37
    | spl10_2
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f886,f648,f100,f393,f888])).

fof(f888,plain,
    ( spl10_86
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f648,plain,
    ( spl10_62
  <=> sK5 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f886,plain,
    ( ~ sP0(k1_xboole_0,sK7)
    | k1_xboole_0 = sK7
    | spl10_2
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f885,f733])).

fof(f733,plain,
    ( ! [X1] :
        ( v1_funct_2(sK7,sK5,X1)
        | ~ sP0(X1,sK7) )
    | ~ spl10_62 ),
    inference(superposition,[],[f71,f650])).

fof(f650,plain,
    ( sK5 = k1_relat_1(sK7)
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f648])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f885,plain,
    ( ~ sP0(k1_xboole_0,sK7)
    | ~ v1_funct_2(sK7,sK5,k1_xboole_0)
    | k1_xboole_0 = sK7
    | spl10_2
    | ~ spl10_62 ),
    inference(subsumption_resolution,[],[f796,f102])).

fof(f796,plain,
    ( ~ sP0(k1_xboole_0,sK7)
    | ~ v1_funct_2(sK7,sK5,k1_xboole_0)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK7
    | ~ spl10_62 ),
    inference(resolution,[],[f789,f92])).

fof(f92,plain,(
    ! [X2,X0] :
      ( ~ sP3(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f789,plain,
    ( ! [X1] :
        ( sP3(sK7,X1,sK5)
        | ~ sP0(X1,sK7) )
    | ~ spl10_62 ),
    inference(resolution,[],[f732,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f34,f41,f40,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f732,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0)))
        | ~ sP0(X0,sK7) )
    | ~ spl10_62 ),
    inference(superposition,[],[f72,f650])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f848,plain,
    ( ~ spl10_36
    | spl10_79
    | ~ spl10_13
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f731,f648,f155,f844,f381])).

fof(f381,plain,
    ( spl10_36
  <=> v1_xboole_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f844,plain,
    ( spl10_79
  <=> sK5 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f155,plain,
    ( spl10_13
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f731,plain,
    ( sK5 = sK7
    | ~ v1_xboole_0(sK7)
    | ~ spl10_13
    | ~ spl10_62 ),
    inference(superposition,[],[f650,f162])).

fof(f162,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl10_13 ),
    inference(superposition,[],[f157,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f157,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f155])).

fof(f839,plain,
    ( spl10_78
    | ~ spl10_9
    | ~ spl10_15
    | ~ spl10_68
    | ~ spl10_69
    | spl10_77 ),
    inference(avatar_split_clause,[],[f829,f823,f700,f695,f180,f135,f836])).

fof(f180,plain,
    ( spl10_15
  <=> r2_hidden(sK9,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f695,plain,
    ( spl10_68
  <=> v1_funct_2(sK7,sK5,k1_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

% (5543)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f700,plain,
    ( spl10_69
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f829,plain,
    ( r2_hidden(k1_funct_1(sK7,sK9),k1_relat_1(sK8))
    | ~ spl10_9
    | ~ spl10_15
    | ~ spl10_68
    | ~ spl10_69
    | spl10_77 ),
    inference(unit_resulting_resolution,[],[f137,f182,f697,f702,f824,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),X1)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f824,plain,
    ( k1_xboole_0 != k1_relat_1(sK8)
    | spl10_77 ),
    inference(avatar_component_clause,[],[f823])).

fof(f702,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8))))
    | ~ spl10_69 ),
    inference(avatar_component_clause,[],[f700])).

fof(f697,plain,
    ( v1_funct_2(sK7,sK5,k1_relat_1(sK8))
    | ~ spl10_68 ),
    inference(avatar_component_clause,[],[f695])).

fof(f182,plain,
    ( r2_hidden(sK9,sK5)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f180])).

fof(f724,plain,
    ( k1_xboole_0 != sK6
    | v1_xboole_0(sK6)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f703,plain,
    ( spl10_69
    | ~ spl10_54
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f683,f648,f541,f700])).

fof(f541,plain,
    ( spl10_54
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f683,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8))))
    | ~ spl10_54
    | ~ spl10_62 ),
    inference(backward_demodulation,[],[f543,f650])).

fof(f543,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8))))
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f541])).

fof(f698,plain,
    ( spl10_68
    | ~ spl10_49
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f682,f648,f505,f695])).

fof(f505,plain,
    ( spl10_49
  <=> v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f682,plain,
    ( v1_funct_2(sK7,sK5,k1_relat_1(sK8))
    | ~ spl10_49
    | ~ spl10_62 ),
    inference(backward_demodulation,[],[f507,f650])).

% (5541)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f507,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f505])).

fof(f680,plain,
    ( spl10_66
    | ~ spl10_61 ),
    inference(avatar_split_clause,[],[f674,f644,f676])).

fof(f676,plain,
    ( spl10_66
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f644,plain,
    ( spl10_61
  <=> sP1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f674,plain,
    ( k1_xboole_0 = sK6
    | ~ spl10_61 ),
    inference(resolution,[],[f646,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f646,plain,
    ( sP1(sK5,sK6)
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f644])).

fof(f668,plain,
    ( spl10_61
    | spl10_62
    | ~ spl10_8
    | ~ spl10_27
    | ~ spl10_47 ),
    inference(avatar_split_clause,[],[f667,f494,f295,f130,f648,f644])).

fof(f295,plain,
    ( spl10_27
  <=> sP2(sK5,sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f494,plain,
    ( spl10_47
  <=> k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f667,plain,
    ( sK5 = k1_relat_1(sK7)
    | sP1(sK5,sK6)
    | ~ spl10_8
    | ~ spl10_27
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f666,f297])).

fof(f297,plain,
    ( sP2(sK5,sK7,sK6)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f295])).

fof(f666,plain,
    ( sK5 = k1_relat_1(sK7)
    | sP1(sK5,sK6)
    | ~ sP2(sK5,sK7,sK6)
    | ~ spl10_8
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f638,f132])).

fof(f638,plain,
    ( sK5 = k1_relat_1(sK7)
    | ~ v1_funct_2(sK7,sK5,sK6)
    | sP1(sK5,sK6)
    | ~ sP2(sK5,sK7,sK6)
    | ~ spl10_47 ),
    inference(superposition,[],[f496,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f496,plain,
    ( k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7)
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f494])).

fof(f544,plain,
    ( spl10_54
    | ~ spl10_45
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f538,f499,f475,f541])).

fof(f475,plain,
    ( spl10_45
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f538,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8))))
    | ~ spl10_45
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f477,f501])).

fof(f477,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f475])).

fof(f532,plain,
    ( spl10_53
    | ~ spl10_5
    | ~ spl10_41 ),
    inference(avatar_split_clause,[],[f527,f434,f115,f529])).

fof(f434,plain,
    ( spl10_41
  <=> r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f527,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8))
    | ~ spl10_5
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f492,f117])).

fof(f492,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ spl10_41 ),
    inference(superposition,[],[f436,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f436,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f434])).

fof(f520,plain,
    ( spl10_51
    | ~ spl10_5
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f515,f450,f115,f517])).

fof(f450,plain,
    ( spl10_43
  <=> sP0(k1_relset_1(sK6,sK4,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f515,plain,
    ( sP0(k1_relat_1(sK8),sK7)
    | ~ spl10_5
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f490,f117])).

fof(f490,plain,
    ( sP0(k1_relat_1(sK8),sK7)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ spl10_43 ),
    inference(superposition,[],[f452,f78])).

fof(f452,plain,
    ( sP0(k1_relset_1(sK6,sK4,sK8),sK7)
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f450])).

fof(f508,plain,
    ( spl10_49
    | ~ spl10_5
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f503,f470,f115,f505])).

fof(f470,plain,
    ( spl10_44
  <=> v1_funct_2(sK7,k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f503,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8))
    | ~ spl10_5
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f488,f117])).

fof(f488,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ spl10_44 ),
    inference(superposition,[],[f472,f78])).

fof(f472,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f470])).

fof(f502,plain,
    ( spl10_48
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f486,f115,f499])).

fof(f486,plain,
    ( k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8)
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f117,f78])).

fof(f497,plain,
    ( spl10_47
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f487,f125,f494])).

fof(f487,plain,
    ( k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7)
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f127,f78])).

fof(f478,plain,
    ( spl10_45
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f462,f450,f475])).

fof(f462,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))))
    | ~ spl10_43 ),
    inference(unit_resulting_resolution,[],[f452,f72])).

fof(f473,plain,
    ( spl10_44
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f463,f450,f470])).

fof(f463,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ spl10_43 ),
    inference(unit_resulting_resolution,[],[f452,f71])).

fof(f456,plain,
    ( spl10_43
    | ~ spl10_9
    | ~ spl10_16
    | ~ spl10_41 ),
    inference(avatar_split_clause,[],[f455,f434,f192,f135,f450])).

fof(f192,plain,
    ( spl10_16
  <=> v1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f455,plain,
    ( sP0(k1_relset_1(sK6,sK4,sK8),sK7)
    | ~ spl10_9
    | ~ spl10_16
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f454,f194])).

fof(f194,plain,
    ( v1_relat_1(sK7)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f454,plain,
    ( sP0(k1_relset_1(sK6,sK4,sK8),sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl10_9
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f441,f137])).

fof(f441,plain,
    ( sP0(k1_relset_1(sK6,sK4,sK8),sK7)
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | ~ spl10_41 ),
    inference(resolution,[],[f436,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP0(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f24,f37])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f437,plain,
    ( spl10_41
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f432,f125,f105,f434])).

fof(f105,plain,
    ( spl10_3
  <=> r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f432,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f421,f127])).

fof(f421,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ spl10_3 ),
    inference(superposition,[],[f107,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f107,plain,
    ( r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f426,plain,
    ( spl10_39
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f420,f125,f423])).

fof(f420,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7)
    | ~ spl10_7 ),
    inference(unit_resulting_resolution,[],[f127,f77])).

fof(f397,plain,
    ( ~ spl10_37
    | ~ spl10_11
    | spl10_36 ),
    inference(avatar_split_clause,[],[f390,f381,f145,f393])).

fof(f145,plain,
    ( spl10_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f390,plain,
    ( ~ sP0(k1_xboole_0,sK7)
    | ~ spl10_11
    | spl10_36 ),
    inference(resolution,[],[f386,f72])).

fof(f386,plain,
    ( ! [X0] : ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ spl10_11
    | spl10_36 ),
    inference(unit_resulting_resolution,[],[f147,f383,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f383,plain,
    ( ~ v1_xboole_0(sK7)
    | spl10_36 ),
    inference(avatar_component_clause,[],[f381])).

fof(f147,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f304,plain,
    ( spl10_27
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f292,f125,f295])).

fof(f292,plain,
    ( sP2(sK5,sK7,sK6)
    | ~ spl10_7 ),
    inference(resolution,[],[f87,f127])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f233,plain,
    ( spl10_21
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f221,f115,f229])).

fof(f221,plain,
    ( v5_relat_1(sK8,sK4)
    | ~ spl10_5 ),
    inference(resolution,[],[f80,f117])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f202,plain,
    ( spl10_16
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f190,f125,f192])).

fof(f190,plain,
    ( v1_relat_1(sK7)
    | ~ spl10_7 ),
    inference(resolution,[],[f76,f127])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f201,plain,
    ( spl10_17
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f189,f115,f197])).

fof(f189,plain,
    ( v1_relat_1(sK8)
    | ~ spl10_5 ),
    inference(resolution,[],[f76,f117])).

fof(f183,plain,
    ( spl10_15
    | ~ spl10_4
    | spl10_14 ),
    inference(avatar_split_clause,[],[f178,f167,f110,f180])).

fof(f167,plain,
    ( spl10_14
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

% (5534)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (5526)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% (5524)Termination reason: Refutation not found, incomplete strategy

% (5524)Memory used [KB]: 10746
% (5524)Time elapsed: 0.074 s
% (5524)------------------------------
% (5524)------------------------------
% (5525)Refutation not found, incomplete strategy% (5525)------------------------------
% (5525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5525)Termination reason: Refutation not found, incomplete strategy

% (5525)Memory used [KB]: 10874
% (5525)Time elapsed: 0.071 s
% (5525)------------------------------
% (5525)------------------------------
% (5534)Refutation not found, incomplete strategy% (5534)------------------------------
% (5534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5534)Termination reason: Refutation not found, incomplete strategy

% (5534)Memory used [KB]: 10874
% (5534)Time elapsed: 0.095 s
% (5534)------------------------------
% (5534)------------------------------
% (5537)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f178,plain,
    ( r2_hidden(sK9,sK5)
    | ~ spl10_4
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f112,f169,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f169,plain,
    ( ~ v1_xboole_0(sK5)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f170,plain,
    ( ~ spl10_14
    | spl10_2 ),
    inference(avatar_split_clause,[],[f160,f100,f167])).

fof(f160,plain,
    ( ~ v1_xboole_0(sK5)
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f102,f67])).

fof(f158,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f65,f155])).

fof(f65,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f148,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f64,f145])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f143,plain,(
    ~ spl10_10 ),
    inference(avatar_split_clause,[],[f54,f140])).

fof(f54,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
    & k1_xboole_0 != sK5
    & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
    & m1_subset_1(sK9,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f18,f46,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK5
                  & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4))
                  & m1_subset_1(X5,sK5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK5
                & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4))
                & m1_subset_1(X5,sK5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X3,sK5,sK6)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(sK7,X5))
              & k1_xboole_0 != sK5
              & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,X4))
              & m1_subset_1(X5,sK5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(sK7,X5))
            & k1_xboole_0 != sK5
            & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,X4))
            & m1_subset_1(X5,sK5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X5) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,X5))
          & k1_xboole_0 != sK5
          & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
          & m1_subset_1(X5,sK5) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X5) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,X5))
        & k1_xboole_0 != sK5
        & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
        & m1_subset_1(X5,sK5) )
   => ( k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))
      & k1_xboole_0 != sK5
      & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))
      & m1_subset_1(sK9,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f138,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f55,f135])).

fof(f55,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f133,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f56,f130])).

fof(f56,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f128,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f57,f125])).

fof(f57,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f47])).

fof(f123,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f58,f120])).

fof(f58,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f47])).

fof(f118,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f59,f115])).

fof(f59,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f47])).

fof(f113,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f60,f110])).

fof(f60,plain,(
    m1_subset_1(sK9,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f61,f105])).

fof(f61,plain,(
    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f62,f100])).

fof(f62,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f63,f95])).

fof(f63,plain,(
    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:26:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (5531)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.46  % (5539)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.46  % (5527)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (5538)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (5536)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (5533)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (5529)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (5539)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (5528)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (5535)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (5542)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (5524)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  % (5532)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (5525)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  fof(f1085,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f158,f170,f183,f201,f202,f233,f304,f397,f426,f437,f456,f473,f478,f497,f502,f508,f520,f532,f544,f668,f680,f698,f703,f724,f839,f848,f891,f919,f986,f1082,f1084])).
% 0.22/0.48  % (5524)Refutation not found, incomplete strategy% (5524)------------------------------
% 0.22/0.48  % (5524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5523)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  fof(f1084,plain,(
% 0.22/0.48    k1_xboole_0 != sK7 | sK5 != sK7 | k1_xboole_0 = sK5),
% 0.22/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.48  fof(f1082,plain,(
% 0.22/0.48    ~spl10_6 | ~spl10_17 | ~spl10_21 | ~spl10_78 | spl10_96),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f1081])).
% 0.22/0.48  fof(f1081,plain,(
% 0.22/0.48    $false | (~spl10_6 | ~spl10_17 | ~spl10_21 | ~spl10_78 | spl10_96)),
% 0.22/0.48    inference(subsumption_resolution,[],[f1079,f985])).
% 0.22/0.48  fof(f985,plain,(
% 0.22/0.48    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | spl10_96),
% 0.22/0.48    inference(avatar_component_clause,[],[f983])).
% 0.22/0.48  % (5535)Refutation not found, incomplete strategy% (5535)------------------------------
% 0.22/0.48  % (5535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5535)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (5535)Memory used [KB]: 6140
% 0.22/0.48  % (5535)Time elapsed: 0.080 s
% 0.22/0.48  % (5535)------------------------------
% 0.22/0.48  % (5535)------------------------------
% 0.22/0.48  fof(f983,plain,(
% 0.22/0.48    spl10_96 <=> k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).
% 0.22/0.48  fof(f1079,plain,(
% 0.22/0.48    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) = k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | (~spl10_6 | ~spl10_17 | ~spl10_21 | ~spl10_78)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f199,f231,f122,f838,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.22/0.48  fof(f838,plain,(
% 0.22/0.48    r2_hidden(k1_funct_1(sK7,sK9),k1_relat_1(sK8)) | ~spl10_78),
% 0.22/0.48    inference(avatar_component_clause,[],[f836])).
% 0.22/0.48  fof(f836,plain,(
% 0.22/0.48    spl10_78 <=> r2_hidden(k1_funct_1(sK7,sK9),k1_relat_1(sK8))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    v1_funct_1(sK8) | ~spl10_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl10_6 <=> v1_funct_1(sK8)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.48  fof(f231,plain,(
% 0.22/0.48    v5_relat_1(sK8,sK4) | ~spl10_21),
% 0.22/0.48    inference(avatar_component_clause,[],[f229])).
% 0.22/0.48  fof(f229,plain,(
% 0.22/0.48    spl10_21 <=> v5_relat_1(sK8,sK4)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    v1_relat_1(sK8) | ~spl10_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f197])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    spl10_17 <=> v1_relat_1(sK8)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.22/0.49  fof(f986,plain,(
% 0.22/0.49    ~spl10_96 | spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10 | ~spl10_39 | ~spl10_48 | ~spl10_53),
% 0.22/0.49    inference(avatar_split_clause,[],[f981,f529,f499,f423,f140,f135,f130,f125,f120,f115,f110,f100,f95,f983])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl10_1 <=> k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) = k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl10_2 <=> k1_xboole_0 = sK5),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl10_4 <=> m1_subset_1(sK9,sK5)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl10_5 <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    spl10_7 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    spl10_8 <=> v1_funct_2(sK7,sK5,sK6)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    spl10_9 <=> v1_funct_1(sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    spl10_10 <=> v1_xboole_0(sK6)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.22/0.49  fof(f423,plain,(
% 0.22/0.49    spl10_39 <=> k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 0.22/0.49  fof(f499,plain,(
% 0.22/0.49    spl10_48 <=> k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 0.22/0.49  fof(f529,plain,(
% 0.22/0.49    spl10_53 <=> r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).
% 0.22/0.49  fof(f981,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | (spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10 | ~spl10_39 | ~spl10_48 | ~spl10_53)),
% 0.22/0.49    inference(subsumption_resolution,[],[f980,f531])).
% 0.22/0.49  fof(f531,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) | ~spl10_53),
% 0.22/0.49    inference(avatar_component_clause,[],[f529])).
% 0.22/0.49  % (5530)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  fof(f980,plain,(
% 0.22/0.49    ~r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) | k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | (spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10 | ~spl10_39 | ~spl10_48)),
% 0.22/0.49    inference(forward_demodulation,[],[f979,f425])).
% 0.22/0.49  fof(f425,plain,(
% 0.22/0.49    k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) | ~spl10_39),
% 0.22/0.49    inference(avatar_component_clause,[],[f423])).
% 0.22/0.49  fof(f979,plain,(
% 0.22/0.49    ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relat_1(sK8)) | k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | (spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10 | ~spl10_48)),
% 0.22/0.49    inference(forward_demodulation,[],[f978,f501])).
% 0.22/0.49  fof(f501,plain,(
% 0.22/0.49    k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) | ~spl10_48),
% 0.22/0.49    inference(avatar_component_clause,[],[f499])).
% 0.22/0.49  fof(f978,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | (spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f977,f142])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ~v1_xboole_0(sK6) | spl10_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f140])).
% 0.22/0.49  fof(f977,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | v1_xboole_0(sK6) | (spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9)),
% 0.22/0.49    inference(subsumption_resolution,[],[f976,f137])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    v1_funct_1(sK7) | ~spl10_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f135])).
% 0.22/0.49  fof(f976,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~v1_funct_1(sK7) | v1_xboole_0(sK6) | (spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8)),
% 0.22/0.49    inference(subsumption_resolution,[],[f975,f132])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    v1_funct_2(sK7,sK5,sK6) | ~spl10_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f130])).
% 0.22/0.49  fof(f975,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK6) | (spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f974,f127])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~spl10_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f125])).
% 0.22/0.49  fof(f974,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK6) | (spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5 | ~spl10_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f973,f122])).
% 0.22/0.49  fof(f973,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK6) | (spl10_1 | spl10_2 | ~spl10_4 | ~spl10_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f972,f117])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~spl10_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f115])).
% 0.22/0.49  fof(f972,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK6) | (spl10_1 | spl10_2 | ~spl10_4)),
% 0.22/0.49    inference(subsumption_resolution,[],[f971,f112])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    m1_subset_1(sK9,sK5) | ~spl10_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f110])).
% 0.22/0.49  fof(f971,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~m1_subset_1(sK9,sK5) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK6) | (spl10_1 | spl10_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f970,f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    k1_xboole_0 != sK5 | spl10_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f100])).
% 0.22/0.49  fof(f970,plain,(
% 0.22/0.49    k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) != k1_funct_1(sK8,k1_funct_1(sK7,sK9)) | k1_xboole_0 = sK5 | ~r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~m1_subset_1(sK9,sK5) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK6) | spl10_1),
% 0.22/0.49    inference(superposition,[],[f97,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  % (5540)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) | spl10_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f95])).
% 0.22/0.49  fof(f919,plain,(
% 0.22/0.49    spl10_37 | ~spl10_51 | ~spl10_77),
% 0.22/0.49    inference(avatar_split_clause,[],[f896,f823,f517,f393])).
% 0.22/0.49  fof(f393,plain,(
% 0.22/0.49    spl10_37 <=> sP0(k1_xboole_0,sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).
% 0.22/0.49  fof(f517,plain,(
% 0.22/0.49    spl10_51 <=> sP0(k1_relat_1(sK8),sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).
% 0.22/0.49  fof(f823,plain,(
% 0.22/0.49    spl10_77 <=> k1_xboole_0 = k1_relat_1(sK8)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).
% 0.22/0.49  fof(f896,plain,(
% 0.22/0.49    sP0(k1_xboole_0,sK7) | (~spl10_51 | ~spl10_77)),
% 0.22/0.49    inference(backward_demodulation,[],[f519,f825])).
% 0.22/0.49  fof(f825,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(sK8) | ~spl10_77),
% 0.22/0.49    inference(avatar_component_clause,[],[f823])).
% 0.22/0.49  fof(f519,plain,(
% 0.22/0.49    sP0(k1_relat_1(sK8),sK7) | ~spl10_51),
% 0.22/0.49    inference(avatar_component_clause,[],[f517])).
% 0.22/0.49  fof(f891,plain,(
% 0.22/0.49    spl10_86 | ~spl10_37 | spl10_2 | ~spl10_62),
% 0.22/0.49    inference(avatar_split_clause,[],[f886,f648,f100,f393,f888])).
% 0.22/0.49  fof(f888,plain,(
% 0.22/0.49    spl10_86 <=> k1_xboole_0 = sK7),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).
% 0.22/0.49  fof(f648,plain,(
% 0.22/0.49    spl10_62 <=> sK5 = k1_relat_1(sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).
% 0.22/0.49  fof(f886,plain,(
% 0.22/0.49    ~sP0(k1_xboole_0,sK7) | k1_xboole_0 = sK7 | (spl10_2 | ~spl10_62)),
% 0.22/0.49    inference(subsumption_resolution,[],[f885,f733])).
% 0.22/0.49  fof(f733,plain,(
% 0.22/0.49    ( ! [X1] : (v1_funct_2(sK7,sK5,X1) | ~sP0(X1,sK7)) ) | ~spl10_62),
% 0.22/0.49    inference(superposition,[],[f71,f650])).
% 0.22/0.49  fof(f650,plain,(
% 0.22/0.49    sK5 = k1_relat_1(sK7) | ~spl10_62),
% 0.22/0.49    inference(avatar_component_clause,[],[f648])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.49  fof(f885,plain,(
% 0.22/0.49    ~sP0(k1_xboole_0,sK7) | ~v1_funct_2(sK7,sK5,k1_xboole_0) | k1_xboole_0 = sK7 | (spl10_2 | ~spl10_62)),
% 0.22/0.49    inference(subsumption_resolution,[],[f796,f102])).
% 0.22/0.49  fof(f796,plain,(
% 0.22/0.49    ~sP0(k1_xboole_0,sK7) | ~v1_funct_2(sK7,sK5,k1_xboole_0) | k1_xboole_0 = sK5 | k1_xboole_0 = sK7 | ~spl10_62),
% 0.22/0.49    inference(resolution,[],[f789,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~sP3(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(equality_resolution,[],[f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP3(X0,X1,X2))),
% 0.22/0.49    inference(rectify,[],[f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.49  fof(f789,plain,(
% 0.22/0.49    ( ! [X1] : (sP3(sK7,X1,sK5) | ~sP0(X1,sK7)) ) | ~spl10_62),
% 0.22/0.49    inference(resolution,[],[f732,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP3(X2,X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(definition_folding,[],[f34,f41,f40,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.22/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.49  fof(f732,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,X0))) | ~sP0(X0,sK7)) ) | ~spl10_62),
% 0.22/0.49    inference(superposition,[],[f72,f650])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f48])).
% 0.22/0.49  fof(f848,plain,(
% 0.22/0.49    ~spl10_36 | spl10_79 | ~spl10_13 | ~spl10_62),
% 0.22/0.49    inference(avatar_split_clause,[],[f731,f648,f155,f844,f381])).
% 0.22/0.49  fof(f381,plain,(
% 0.22/0.49    spl10_36 <=> v1_xboole_0(sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 0.22/0.49  fof(f844,plain,(
% 0.22/0.49    spl10_79 <=> sK5 = sK7),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    spl10_13 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.22/0.49  fof(f731,plain,(
% 0.22/0.49    sK5 = sK7 | ~v1_xboole_0(sK7) | (~spl10_13 | ~spl10_62)),
% 0.22/0.49    inference(superposition,[],[f650,f162])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ( ! [X0] : (k1_relat_1(X0) = X0 | ~v1_xboole_0(X0)) ) | ~spl10_13),
% 0.22/0.49    inference(superposition,[],[f157,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl10_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f155])).
% 0.22/0.49  fof(f839,plain,(
% 0.22/0.49    spl10_78 | ~spl10_9 | ~spl10_15 | ~spl10_68 | ~spl10_69 | spl10_77),
% 0.22/0.49    inference(avatar_split_clause,[],[f829,f823,f700,f695,f180,f135,f836])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    spl10_15 <=> r2_hidden(sK9,sK5)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.22/0.49  fof(f695,plain,(
% 0.22/0.49    spl10_68 <=> v1_funct_2(sK7,sK5,k1_relat_1(sK8))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).
% 0.22/0.49  % (5543)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.49  fof(f700,plain,(
% 0.22/0.49    spl10_69 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).
% 0.22/0.49  fof(f829,plain,(
% 0.22/0.49    r2_hidden(k1_funct_1(sK7,sK9),k1_relat_1(sK8)) | (~spl10_9 | ~spl10_15 | ~spl10_68 | ~spl10_69 | spl10_77)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f137,f182,f697,f702,f824,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),X1) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.49    inference(flattening,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 0.22/0.49  fof(f824,plain,(
% 0.22/0.49    k1_xboole_0 != k1_relat_1(sK8) | spl10_77),
% 0.22/0.49    inference(avatar_component_clause,[],[f823])).
% 0.22/0.49  fof(f702,plain,(
% 0.22/0.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8)))) | ~spl10_69),
% 0.22/0.49    inference(avatar_component_clause,[],[f700])).
% 0.22/0.49  fof(f697,plain,(
% 0.22/0.49    v1_funct_2(sK7,sK5,k1_relat_1(sK8)) | ~spl10_68),
% 0.22/0.49    inference(avatar_component_clause,[],[f695])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    r2_hidden(sK9,sK5) | ~spl10_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f180])).
% 0.22/0.49  fof(f724,plain,(
% 0.22/0.49    k1_xboole_0 != sK6 | v1_xboole_0(sK6) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f703,plain,(
% 0.22/0.49    spl10_69 | ~spl10_54 | ~spl10_62),
% 0.22/0.49    inference(avatar_split_clause,[],[f683,f648,f541,f700])).
% 0.22/0.49  fof(f541,plain,(
% 0.22/0.49    spl10_54 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).
% 0.22/0.49  fof(f683,plain,(
% 0.22/0.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_relat_1(sK8)))) | (~spl10_54 | ~spl10_62)),
% 0.22/0.49    inference(backward_demodulation,[],[f543,f650])).
% 0.22/0.49  fof(f543,plain,(
% 0.22/0.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8)))) | ~spl10_54),
% 0.22/0.49    inference(avatar_component_clause,[],[f541])).
% 0.22/0.49  fof(f698,plain,(
% 0.22/0.49    spl10_68 | ~spl10_49 | ~spl10_62),
% 0.22/0.49    inference(avatar_split_clause,[],[f682,f648,f505,f695])).
% 0.22/0.49  fof(f505,plain,(
% 0.22/0.49    spl10_49 <=> v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).
% 0.22/0.49  fof(f682,plain,(
% 0.22/0.49    v1_funct_2(sK7,sK5,k1_relat_1(sK8)) | (~spl10_49 | ~spl10_62)),
% 0.22/0.49    inference(backward_demodulation,[],[f507,f650])).
% 0.22/0.49  % (5541)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  fof(f507,plain,(
% 0.22/0.49    v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8)) | ~spl10_49),
% 0.22/0.49    inference(avatar_component_clause,[],[f505])).
% 0.22/0.49  fof(f680,plain,(
% 0.22/0.49    spl10_66 | ~spl10_61),
% 0.22/0.49    inference(avatar_split_clause,[],[f674,f644,f676])).
% 0.22/0.49  fof(f676,plain,(
% 0.22/0.49    spl10_66 <=> k1_xboole_0 = sK6),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).
% 0.22/0.49  fof(f644,plain,(
% 0.22/0.49    spl10_61 <=> sP1(sK5,sK6)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).
% 0.22/0.49  fof(f674,plain,(
% 0.22/0.49    k1_xboole_0 = sK6 | ~spl10_61),
% 0.22/0.49    inference(resolution,[],[f646,f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f39])).
% 0.22/0.49  fof(f646,plain,(
% 0.22/0.49    sP1(sK5,sK6) | ~spl10_61),
% 0.22/0.49    inference(avatar_component_clause,[],[f644])).
% 0.22/0.49  fof(f668,plain,(
% 0.22/0.49    spl10_61 | spl10_62 | ~spl10_8 | ~spl10_27 | ~spl10_47),
% 0.22/0.49    inference(avatar_split_clause,[],[f667,f494,f295,f130,f648,f644])).
% 0.22/0.49  fof(f295,plain,(
% 0.22/0.49    spl10_27 <=> sP2(sK5,sK7,sK6)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.22/0.49  fof(f494,plain,(
% 0.22/0.49    spl10_47 <=> k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 0.22/0.49  fof(f667,plain,(
% 0.22/0.49    sK5 = k1_relat_1(sK7) | sP1(sK5,sK6) | (~spl10_8 | ~spl10_27 | ~spl10_47)),
% 0.22/0.49    inference(subsumption_resolution,[],[f666,f297])).
% 0.22/0.49  fof(f297,plain,(
% 0.22/0.49    sP2(sK5,sK7,sK6) | ~spl10_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f295])).
% 0.22/0.49  fof(f666,plain,(
% 0.22/0.49    sK5 = k1_relat_1(sK7) | sP1(sK5,sK6) | ~sP2(sK5,sK7,sK6) | (~spl10_8 | ~spl10_47)),
% 0.22/0.49    inference(subsumption_resolution,[],[f638,f132])).
% 0.22/0.49  fof(f638,plain,(
% 0.22/0.49    sK5 = k1_relat_1(sK7) | ~v1_funct_2(sK7,sK5,sK6) | sP1(sK5,sK6) | ~sP2(sK5,sK7,sK6) | ~spl10_47),
% 0.22/0.49    inference(superposition,[],[f496,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.22/0.49    inference(rectify,[],[f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f40])).
% 0.22/0.49  fof(f496,plain,(
% 0.22/0.49    k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7) | ~spl10_47),
% 0.22/0.49    inference(avatar_component_clause,[],[f494])).
% 0.22/0.49  fof(f544,plain,(
% 0.22/0.49    spl10_54 | ~spl10_45 | ~spl10_48),
% 0.22/0.49    inference(avatar_split_clause,[],[f538,f499,f475,f541])).
% 0.22/0.49  fof(f475,plain,(
% 0.22/0.49    spl10_45 <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).
% 0.22/0.49  fof(f538,plain,(
% 0.22/0.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relat_1(sK8)))) | (~spl10_45 | ~spl10_48)),
% 0.22/0.49    inference(backward_demodulation,[],[f477,f501])).
% 0.22/0.49  fof(f477,plain,(
% 0.22/0.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)))) | ~spl10_45),
% 0.22/0.49    inference(avatar_component_clause,[],[f475])).
% 0.22/0.49  fof(f532,plain,(
% 0.22/0.49    spl10_53 | ~spl10_5 | ~spl10_41),
% 0.22/0.49    inference(avatar_split_clause,[],[f527,f434,f115,f529])).
% 0.22/0.49  fof(f434,plain,(
% 0.22/0.49    spl10_41 <=> r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 0.22/0.49  fof(f527,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) | (~spl10_5 | ~spl10_41)),
% 0.22/0.49    inference(subsumption_resolution,[],[f492,f117])).
% 0.22/0.49  fof(f492,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK7),k1_relat_1(sK8)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~spl10_41),
% 0.22/0.49    inference(superposition,[],[f436,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f436,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) | ~spl10_41),
% 0.22/0.49    inference(avatar_component_clause,[],[f434])).
% 0.22/0.49  fof(f520,plain,(
% 0.22/0.49    spl10_51 | ~spl10_5 | ~spl10_43),
% 0.22/0.49    inference(avatar_split_clause,[],[f515,f450,f115,f517])).
% 0.22/0.49  fof(f450,plain,(
% 0.22/0.49    spl10_43 <=> sP0(k1_relset_1(sK6,sK4,sK8),sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).
% 0.22/0.49  fof(f515,plain,(
% 0.22/0.49    sP0(k1_relat_1(sK8),sK7) | (~spl10_5 | ~spl10_43)),
% 0.22/0.49    inference(subsumption_resolution,[],[f490,f117])).
% 0.22/0.49  fof(f490,plain,(
% 0.22/0.49    sP0(k1_relat_1(sK8),sK7) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~spl10_43),
% 0.22/0.49    inference(superposition,[],[f452,f78])).
% 0.22/0.49  fof(f452,plain,(
% 0.22/0.49    sP0(k1_relset_1(sK6,sK4,sK8),sK7) | ~spl10_43),
% 0.22/0.49    inference(avatar_component_clause,[],[f450])).
% 0.22/0.49  fof(f508,plain,(
% 0.22/0.49    spl10_49 | ~spl10_5 | ~spl10_44),
% 0.22/0.49    inference(avatar_split_clause,[],[f503,f470,f115,f505])).
% 0.22/0.49  fof(f470,plain,(
% 0.22/0.49    spl10_44 <=> v1_funct_2(sK7,k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 0.22/0.49  fof(f503,plain,(
% 0.22/0.49    v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8)) | (~spl10_5 | ~spl10_44)),
% 0.22/0.49    inference(subsumption_resolution,[],[f488,f117])).
% 0.22/0.49  fof(f488,plain,(
% 0.22/0.49    v1_funct_2(sK7,k1_relat_1(sK7),k1_relat_1(sK8)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~spl10_44),
% 0.22/0.49    inference(superposition,[],[f472,f78])).
% 0.22/0.49  fof(f472,plain,(
% 0.22/0.49    v1_funct_2(sK7,k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) | ~spl10_44),
% 0.22/0.49    inference(avatar_component_clause,[],[f470])).
% 0.22/0.49  fof(f502,plain,(
% 0.22/0.49    spl10_48 | ~spl10_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f486,f115,f499])).
% 0.22/0.49  fof(f486,plain,(
% 0.22/0.49    k1_relset_1(sK6,sK4,sK8) = k1_relat_1(sK8) | ~spl10_5),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f117,f78])).
% 0.22/0.49  fof(f497,plain,(
% 0.22/0.49    spl10_47 | ~spl10_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f487,f125,f494])).
% 0.22/0.49  fof(f487,plain,(
% 0.22/0.49    k1_relat_1(sK7) = k1_relset_1(sK5,sK6,sK7) | ~spl10_7),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f127,f78])).
% 0.22/0.49  fof(f478,plain,(
% 0.22/0.49    spl10_45 | ~spl10_43),
% 0.22/0.49    inference(avatar_split_clause,[],[f462,f450,f475])).
% 0.22/0.49  fof(f462,plain,(
% 0.22/0.49    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)))) | ~spl10_43),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f452,f72])).
% 0.22/0.49  fof(f473,plain,(
% 0.22/0.49    spl10_44 | ~spl10_43),
% 0.22/0.49    inference(avatar_split_clause,[],[f463,f450,f470])).
% 0.22/0.49  fof(f463,plain,(
% 0.22/0.49    v1_funct_2(sK7,k1_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) | ~spl10_43),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f452,f71])).
% 0.22/0.49  fof(f456,plain,(
% 0.22/0.49    spl10_43 | ~spl10_9 | ~spl10_16 | ~spl10_41),
% 0.22/0.49    inference(avatar_split_clause,[],[f455,f434,f192,f135,f450])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    spl10_16 <=> v1_relat_1(sK7)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.22/0.49  fof(f455,plain,(
% 0.22/0.49    sP0(k1_relset_1(sK6,sK4,sK8),sK7) | (~spl10_9 | ~spl10_16 | ~spl10_41)),
% 0.22/0.49    inference(subsumption_resolution,[],[f454,f194])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    v1_relat_1(sK7) | ~spl10_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f192])).
% 0.22/0.49  fof(f454,plain,(
% 0.22/0.49    sP0(k1_relset_1(sK6,sK4,sK8),sK7) | ~v1_relat_1(sK7) | (~spl10_9 | ~spl10_41)),
% 0.22/0.49    inference(subsumption_resolution,[],[f441,f137])).
% 0.22/0.49  fof(f441,plain,(
% 0.22/0.49    sP0(k1_relset_1(sK6,sK4,sK8),sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | ~spl10_41),
% 0.22/0.49    inference(resolution,[],[f436,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP0(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(definition_folding,[],[f24,f37])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.49  fof(f437,plain,(
% 0.22/0.49    spl10_41 | ~spl10_3 | ~spl10_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f432,f125,f105,f434])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl10_3 <=> r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.49  fof(f432,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) | (~spl10_3 | ~spl10_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f421,f127])).
% 0.22/0.49  fof(f421,plain,(
% 0.22/0.49    r1_tarski(k2_relat_1(sK7),k1_relset_1(sK6,sK4,sK8)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~spl10_3),
% 0.22/0.49    inference(superposition,[],[f107,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) | ~spl10_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f105])).
% 0.22/0.49  fof(f426,plain,(
% 0.22/0.49    spl10_39 | ~spl10_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f420,f125,f423])).
% 0.22/0.49  fof(f420,plain,(
% 0.22/0.49    k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) | ~spl10_7),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f127,f77])).
% 0.22/0.49  fof(f397,plain,(
% 0.22/0.49    ~spl10_37 | ~spl10_11 | spl10_36),
% 0.22/0.49    inference(avatar_split_clause,[],[f390,f381,f145,f393])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    spl10_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.22/0.49  fof(f390,plain,(
% 0.22/0.49    ~sP0(k1_xboole_0,sK7) | (~spl10_11 | spl10_36)),
% 0.22/0.49    inference(resolution,[],[f386,f72])).
% 0.22/0.49  fof(f386,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | (~spl10_11 | spl10_36)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f147,f383,f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.49  fof(f383,plain,(
% 0.22/0.49    ~v1_xboole_0(sK7) | spl10_36),
% 0.22/0.49    inference(avatar_component_clause,[],[f381])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0) | ~spl10_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f145])).
% 0.22/0.49  fof(f304,plain,(
% 0.22/0.49    spl10_27 | ~spl10_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f292,f125,f295])).
% 0.22/0.49  fof(f292,plain,(
% 0.22/0.49    sP2(sK5,sK7,sK6) | ~spl10_7),
% 0.22/0.49    inference(resolution,[],[f87,f127])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    spl10_21 | ~spl10_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f221,f115,f229])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    v5_relat_1(sK8,sK4) | ~spl10_5),
% 0.22/0.49    inference(resolution,[],[f80,f117])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    spl10_16 | ~spl10_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f190,f125,f192])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    v1_relat_1(sK7) | ~spl10_7),
% 0.22/0.49    inference(resolution,[],[f76,f127])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    spl10_17 | ~spl10_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f189,f115,f197])).
% 0.22/0.49  fof(f189,plain,(
% 0.22/0.49    v1_relat_1(sK8) | ~spl10_5),
% 0.22/0.49    inference(resolution,[],[f76,f117])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    spl10_15 | ~spl10_4 | spl10_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f178,f167,f110,f180])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    spl10_14 <=> v1_xboole_0(sK5)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.22/0.49  % (5534)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (5526)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (5524)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (5524)Memory used [KB]: 10746
% 0.22/0.50  % (5524)Time elapsed: 0.074 s
% 0.22/0.50  % (5524)------------------------------
% 0.22/0.50  % (5524)------------------------------
% 0.22/0.50  % (5525)Refutation not found, incomplete strategy% (5525)------------------------------
% 0.22/0.50  % (5525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5525)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (5525)Memory used [KB]: 10874
% 0.22/0.50  % (5525)Time elapsed: 0.071 s
% 0.22/0.50  % (5525)------------------------------
% 0.22/0.50  % (5525)------------------------------
% 0.22/0.50  % (5534)Refutation not found, incomplete strategy% (5534)------------------------------
% 0.22/0.50  % (5534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5534)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (5534)Memory used [KB]: 10874
% 0.22/0.50  % (5534)Time elapsed: 0.095 s
% 0.22/0.50  % (5534)------------------------------
% 0.22/0.50  % (5534)------------------------------
% 0.22/0.50  % (5537)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    r2_hidden(sK9,sK5) | (~spl10_4 | spl10_14)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f112,f169,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    ~v1_xboole_0(sK5) | spl10_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f167])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~spl10_14 | spl10_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f160,f100,f167])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    ~v1_xboole_0(sK5) | spl10_2),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f102,f67])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl10_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f65,f155])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl10_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f64,f145])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ~spl10_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f140])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ~v1_xboole_0(sK6)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    (((k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(sK9,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8,sK9])],[f18,f46,f45,f44,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,X3,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,X3),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(sK7,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,X4),X5) != k7_partfun1(sK4,X4,k1_funct_1(sK7,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,X4)) & m1_subset_1(X5,sK5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X5) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(X5,sK5)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_1(sK8))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ? [X5] : (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),X5) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,X5)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(X5,sK5)) => (k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9)) & k1_xboole_0 != sK5 & r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8)) & m1_subset_1(sK9,sK5))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f15])).
% 0.22/0.50  fof(f15,conjecture,(
% 0.22/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl10_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f135])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    v1_funct_1(sK7)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl10_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f56,f130])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v1_funct_2(sK7,sK5,sK6)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    spl10_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f125])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl10_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f58,f120])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    v1_funct_1(sK8)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl10_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f59,f115])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl10_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f60,f110])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    m1_subset_1(sK9,sK5)),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    spl10_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f105])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    r1_tarski(k2_relset_1(sK5,sK6,sK7),k1_relset_1(sK6,sK4,sK8))),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    ~spl10_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f62,f100])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    k1_xboole_0 != sK5),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~spl10_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f63,f95])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    k1_funct_1(k8_funct_2(sK5,sK6,sK4,sK7,sK8),sK9) != k7_partfun1(sK4,sK8,k1_funct_1(sK7,sK9))),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (5539)------------------------------
% 0.22/0.50  % (5539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5539)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (5539)Memory used [KB]: 11385
% 0.22/0.50  % (5539)Time elapsed: 0.062 s
% 0.22/0.50  % (5539)------------------------------
% 0.22/0.50  % (5539)------------------------------
% 0.22/0.51  % (5522)Success in time 0.141 s
%------------------------------------------------------------------------------
