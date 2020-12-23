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
% DateTime   : Thu Dec  3 13:01:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 295 expanded)
%              Number of leaves         :   46 ( 124 expanded)
%              Depth                    :    9
%              Number of atoms          :  597 (1275 expanded)
%              Number of equality atoms :   91 ( 115 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f861,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f131,f136,f141,f150,f160,f165,f170,f175,f189,f238,f244,f369,f412,f451,f458,f468,f488,f722,f735,f739,f850,f859,f860])).

fof(f860,plain,
    ( k1_xboole_0 != sK2
    | v2_funct_1(sK2)
    | ~ v2_funct_1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f859,plain,
    ( spl4_26
    | ~ spl4_10
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f856,f572,f167,f325])).

fof(f325,plain,
    ( spl4_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f167,plain,
    ( spl4_10
  <=> k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f572,plain,
    ( spl4_47
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f856,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_10
    | ~ spl4_47 ),
    inference(resolution,[],[f573,f261])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f260,f108])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

% (27395)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f260,plain,
    ( ! [X0] :
        ( k9_relat_1(k1_xboole_0,X0) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_10 ),
    inference(superposition,[],[f113,f169])).

fof(f169,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f102,f85])).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f573,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f572])).

fof(f850,plain,
    ( ~ spl4_8
    | spl4_47
    | ~ spl4_66 ),
    inference(avatar_contradiction_clause,[],[f848])).

fof(f848,plain,
    ( $false
    | ~ spl4_8
    | spl4_47
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f574,f773])).

fof(f773,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_8
    | ~ spl4_66 ),
    inference(forward_demodulation,[],[f745,f118])).

fof(f118,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f745,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_8
    | ~ spl4_66 ),
    inference(superposition,[],[f159,f721])).

fof(f721,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f719])).

fof(f719,plain,
    ( spl4_66
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f159,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f574,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_47 ),
    inference(avatar_component_clause,[],[f572])).

fof(f739,plain,(
    spl4_67 ),
    inference(avatar_contradiction_clause,[],[f736])).

fof(f736,plain,
    ( $false
    | spl4_67 ),
    inference(unit_resulting_resolution,[],[f110,f734])).

fof(f734,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_67 ),
    inference(avatar_component_clause,[],[f732])).

fof(f732,plain,
    ( spl4_67
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f110,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f81,f85])).

fof(f81,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f735,plain,
    ( spl4_5
    | ~ spl4_3
    | ~ spl4_1
    | ~ spl4_67
    | ~ spl4_8
    | ~ spl4_33
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f730,f716,f409,f157,f732,f123,f133,f143])).

fof(f143,plain,
    ( spl4_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f133,plain,
    ( spl4_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f123,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f409,plain,
    ( spl4_33
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f716,plain,
    ( spl4_65
  <=> ! [X27,X28] :
        ( v2_funct_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X28,sK1)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X28,sK1)))
        | ~ v2_funct_1(k5_relat_1(X27,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f730,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ spl4_8
    | ~ spl4_33
    | ~ spl4_65 ),
    inference(forward_demodulation,[],[f727,f411])).

fof(f411,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f409])).

fof(f727,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_8
    | ~ spl4_65 ),
    inference(resolution,[],[f717,f159])).

fof(f717,plain,
    ( ! [X28,X27] :
        ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X28,sK1)))
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,X28,sK1)
        | v2_funct_1(X27)
        | ~ v2_funct_1(k5_relat_1(X27,sK3)) )
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f716])).

fof(f722,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_65
    | spl4_66
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f636,f162,f719,f716,f138,f128])).

fof(f128,plain,
    ( spl4_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f138,plain,
    ( spl4_4
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

% (27387)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f162,plain,
    ( spl4_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f636,plain,
    ( ! [X28,X27] :
        ( k1_xboole_0 = sK0
        | v2_funct_1(X27)
        | ~ v2_funct_1(k5_relat_1(X27,sK3))
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X28,sK1)))
        | ~ v1_funct_2(X27,X28,sK1)
        | ~ v1_funct_1(X27) )
    | ~ spl4_9 ),
    inference(resolution,[],[f414,f164])).

fof(f164,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f414,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k5_relat_1(X3,X4))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k5_relat_1(X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(superposition,[],[f76,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f488,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_9
    | spl4_32 ),
    inference(unit_resulting_resolution,[],[f159,f164,f407,f355])).

fof(f355,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f109,f103])).

% (27394)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f407,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_32 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl4_32
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f468,plain,
    ( ~ spl4_17
    | spl4_6
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f462,f455,f147,f215])).

fof(f215,plain,
    ( spl4_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f147,plain,
    ( spl4_6
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f455,plain,
    ( spl4_37
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f462,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_37 ),
    inference(superposition,[],[f278,f457])).

fof(f457,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f455])).

fof(f278,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f252,f114])).

fof(f114,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f252,plain,(
    ! [X2] :
      ( v5_relat_1(X2,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f98,f119])).

fof(f119,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f64])).

% (27395)Refutation not found, incomplete strategy% (27395)------------------------------
% (27395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27395)Termination reason: Refutation not found, incomplete strategy

% (27395)Memory used [KB]: 11001
% (27395)Time elapsed: 0.150 s
% (27395)------------------------------
% (27395)------------------------------
fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f458,plain,
    ( ~ spl4_9
    | spl4_37
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f452,f448,f455,f162])).

fof(f448,plain,
    ( spl4_36
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f452,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_36 ),
    inference(superposition,[],[f450,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f450,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f448])).

fof(f451,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | ~ spl4_9
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_8
    | spl4_36
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f441,f172,f448,f157,f133,f123,f162,f138,f128])).

fof(f172,plain,
    ( spl4_11
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f441,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_11 ),
    inference(resolution,[],[f84,f174])).

fof(f174,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f172])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f412,plain,
    ( ~ spl4_32
    | spl4_33
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f402,f366,f409,f405])).

fof(f366,plain,
    ( spl4_29
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f402,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_29 ),
    inference(resolution,[],[f314,f368])).

fof(f368,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f366])).

fof(f314,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f82,f111])).

fof(f111,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f89,f85])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f369,plain,
    ( ~ spl4_1
    | ~ spl4_8
    | ~ spl4_2
    | ~ spl4_9
    | spl4_29
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f364,f172,f366,f162,f128,f157,f123])).

fof(f364,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f174,f86])).

fof(f244,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f94,f237])).

fof(f237,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl4_20
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f94,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f238,plain,
    ( ~ spl4_20
    | spl4_17
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f198,f162,f215,f235])).

fof(f198,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_9 ),
    inference(resolution,[],[f88,f164])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f189,plain,
    ( spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f184,f167,f186])).

fof(f186,plain,
    ( spl4_13
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f184,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_10 ),
    inference(superposition,[],[f110,f169])).

fof(f175,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f72,f172])).

fof(f72,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f57,f56])).

fof(f56,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

% (27391)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f57,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f170,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f112,f167])).

fof(f112,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f95,f85])).

fof(f95,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f165,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f71,f162])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f160,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f68,f157])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f150,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f73,f147,f143])).

fof(f73,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f141,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f70,f138])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f136,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f67,f133])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f131,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f69,f128])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f126,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f66,f123])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (27390)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.50  % (27382)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.51  % (27374)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (27380)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (27379)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (27371)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (27368)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (27367)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (27368)Refutation not found, incomplete strategy% (27368)------------------------------
% 0.22/0.53  % (27368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27368)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (27368)Memory used [KB]: 1791
% 0.22/0.53  % (27368)Time elapsed: 0.124 s
% 0.22/0.53  % (27368)------------------------------
% 0.22/0.53  % (27368)------------------------------
% 0.22/0.54  % (27372)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (27373)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (27370)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (27389)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (27376)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (27381)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (27383)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (27369)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (27383)Refutation not found, incomplete strategy% (27383)------------------------------
% 0.22/0.55  % (27383)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27383)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27383)Memory used [KB]: 10746
% 0.22/0.55  % (27383)Time elapsed: 0.138 s
% 0.22/0.55  % (27383)------------------------------
% 0.22/0.55  % (27383)------------------------------
% 0.22/0.55  % (27381)Refutation not found, incomplete strategy% (27381)------------------------------
% 0.22/0.55  % (27381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27381)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27381)Memory used [KB]: 1918
% 0.22/0.55  % (27381)Time elapsed: 0.139 s
% 0.22/0.55  % (27381)------------------------------
% 0.22/0.55  % (27381)------------------------------
% 0.22/0.55  % (27386)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (27396)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (27396)Refutation not found, incomplete strategy% (27396)------------------------------
% 0.22/0.55  % (27396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27396)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27396)Memory used [KB]: 1663
% 0.22/0.55  % (27396)Time elapsed: 0.002 s
% 0.22/0.55  % (27396)------------------------------
% 0.22/0.55  % (27396)------------------------------
% 0.22/0.56  % (27392)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.56  % (27384)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (27378)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (27390)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (27375)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f861,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f126,f131,f136,f141,f150,f160,f165,f170,f175,f189,f238,f244,f369,f412,f451,f458,f468,f488,f722,f735,f739,f850,f859,f860])).
% 0.22/0.56  fof(f860,plain,(
% 0.22/0.56    k1_xboole_0 != sK2 | v2_funct_1(sK2) | ~v2_funct_1(k1_xboole_0)),
% 0.22/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.56  fof(f859,plain,(
% 0.22/0.56    spl4_26 | ~spl4_10 | ~spl4_47),
% 0.22/0.56    inference(avatar_split_clause,[],[f856,f572,f167,f325])).
% 0.22/0.56  fof(f325,plain,(
% 0.22/0.56    spl4_26 <=> k1_xboole_0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.22/0.56  fof(f167,plain,(
% 0.22/0.56    spl4_10 <=> k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.56  fof(f572,plain,(
% 0.22/0.56    spl4_47 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.22/0.56  fof(f856,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | (~spl4_10 | ~spl4_47)),
% 0.22/0.56    inference(resolution,[],[f573,f261])).
% 0.22/0.56  fof(f261,plain,(
% 0.22/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_10),
% 0.22/0.56    inference(forward_demodulation,[],[f260,f108])).
% 0.22/0.56  fof(f108,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  % (27395)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.56  fof(f260,plain,(
% 0.22/0.56    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_10),
% 0.22/0.56    inference(superposition,[],[f113,f169])).
% 0.22/0.56  fof(f169,plain,(
% 0.22/0.56    k1_xboole_0 = k6_partfun1(k1_xboole_0) | ~spl4_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f167])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k9_relat_1(k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f102,f85])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,axiom,(
% 0.22/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.22/0.56  fof(f573,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_47),
% 0.22/0.56    inference(avatar_component_clause,[],[f572])).
% 0.22/0.56  fof(f850,plain,(
% 0.22/0.56    ~spl4_8 | spl4_47 | ~spl4_66),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f848])).
% 0.22/0.56  fof(f848,plain,(
% 0.22/0.56    $false | (~spl4_8 | spl4_47 | ~spl4_66)),
% 0.22/0.56    inference(subsumption_resolution,[],[f574,f773])).
% 0.22/0.56  fof(f773,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_8 | ~spl4_66)),
% 0.22/0.56    inference(forward_demodulation,[],[f745,f118])).
% 0.22/0.56  fof(f118,plain,(
% 0.22/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f92])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(flattening,[],[f61])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f745,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_8 | ~spl4_66)),
% 0.22/0.56    inference(superposition,[],[f159,f721])).
% 0.22/0.56  fof(f721,plain,(
% 0.22/0.56    k1_xboole_0 = sK0 | ~spl4_66),
% 0.22/0.56    inference(avatar_component_clause,[],[f719])).
% 0.22/0.56  fof(f719,plain,(
% 0.22/0.56    spl4_66 <=> k1_xboole_0 = sK0),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 0.22/0.56  fof(f159,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f157])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.56  fof(f574,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl4_47),
% 0.22/0.56    inference(avatar_component_clause,[],[f572])).
% 0.22/0.56  fof(f739,plain,(
% 0.22/0.56    spl4_67),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f736])).
% 0.22/0.56  fof(f736,plain,(
% 0.22/0.56    $false | spl4_67),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f110,f734])).
% 0.22/0.56  fof(f734,plain,(
% 0.22/0.56    ~v2_funct_1(k6_partfun1(sK0)) | spl4_67),
% 0.22/0.56    inference(avatar_component_clause,[],[f732])).
% 0.22/0.56  fof(f732,plain,(
% 0.22/0.56    spl4_67 <=> v2_funct_1(k6_partfun1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f81,f85])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,axiom,(
% 0.22/0.56    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 0.22/0.56  fof(f735,plain,(
% 0.22/0.56    spl4_5 | ~spl4_3 | ~spl4_1 | ~spl4_67 | ~spl4_8 | ~spl4_33 | ~spl4_65),
% 0.22/0.56    inference(avatar_split_clause,[],[f730,f716,f409,f157,f732,f123,f133,f143])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    spl4_5 <=> v2_funct_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    spl4_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    spl4_1 <=> v1_funct_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.56  fof(f409,plain,(
% 0.22/0.56    spl4_33 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.22/0.56  fof(f716,plain,(
% 0.22/0.56    spl4_65 <=> ! [X27,X28] : (v2_funct_1(X27) | ~v1_funct_1(X27) | ~v1_funct_2(X27,X28,sK1) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X28,sK1))) | ~v2_funct_1(k5_relat_1(X27,sK3)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.22/0.56  fof(f730,plain,(
% 0.22/0.56    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v2_funct_1(sK2) | (~spl4_8 | ~spl4_33 | ~spl4_65)),
% 0.22/0.56    inference(forward_demodulation,[],[f727,f411])).
% 0.22/0.56  fof(f411,plain,(
% 0.22/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_33),
% 0.22/0.56    inference(avatar_component_clause,[],[f409])).
% 0.22/0.56  fof(f727,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | v2_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_8 | ~spl4_65)),
% 0.22/0.56    inference(resolution,[],[f717,f159])).
% 0.22/0.56  fof(f717,plain,(
% 0.22/0.56    ( ! [X28,X27] : (~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X28,sK1))) | ~v1_funct_1(X27) | ~v1_funct_2(X27,X28,sK1) | v2_funct_1(X27) | ~v2_funct_1(k5_relat_1(X27,sK3))) ) | ~spl4_65),
% 0.22/0.56    inference(avatar_component_clause,[],[f716])).
% 0.22/0.56  fof(f722,plain,(
% 0.22/0.56    ~spl4_2 | ~spl4_4 | spl4_65 | spl4_66 | ~spl4_9),
% 0.22/0.56    inference(avatar_split_clause,[],[f636,f162,f719,f716,f138,f128])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    spl4_2 <=> v1_funct_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    spl4_4 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.56  % (27387)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  fof(f162,plain,(
% 0.22/0.56    spl4_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.56  fof(f636,plain,(
% 0.22/0.56    ( ! [X28,X27] : (k1_xboole_0 = sK0 | v2_funct_1(X27) | ~v2_funct_1(k5_relat_1(X27,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X28,sK1))) | ~v1_funct_2(X27,X28,sK1) | ~v1_funct_1(X27)) ) | ~spl4_9),
% 0.22/0.56    inference(resolution,[],[f414,f164])).
% 0.22/0.56  fof(f164,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f162])).
% 0.22/0.56  fof(f414,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k5_relat_1(X3,X4)) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f413])).
% 0.22/0.56  fof(f413,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k5_relat_1(X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(superposition,[],[f76,f86])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.56    inference(flattening,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.56    inference(ennf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.56    inference(flattening,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 0.22/0.56  fof(f488,plain,(
% 0.22/0.56    ~spl4_8 | ~spl4_9 | spl4_32),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f477])).
% 0.22/0.56  fof(f477,plain,(
% 0.22/0.56    $false | (~spl4_8 | ~spl4_9 | spl4_32)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f159,f164,f407,f355])).
% 0.22/0.56  fof(f355,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f352])).
% 0.22/0.56  fof(f352,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(superposition,[],[f109,f103])).
% 0.22/0.56  % (27394)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.56    inference(ennf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.56    inference(ennf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.22/0.56  fof(f407,plain,(
% 0.22/0.56    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_32),
% 0.22/0.56    inference(avatar_component_clause,[],[f405])).
% 0.22/0.56  fof(f405,plain,(
% 0.22/0.56    spl4_32 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.56  fof(f468,plain,(
% 0.22/0.56    ~spl4_17 | spl4_6 | ~spl4_37),
% 0.22/0.56    inference(avatar_split_clause,[],[f462,f455,f147,f215])).
% 0.22/0.56  fof(f215,plain,(
% 0.22/0.56    spl4_17 <=> v1_relat_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.56  fof(f147,plain,(
% 0.22/0.56    spl4_6 <=> v2_funct_2(sK3,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.56  fof(f455,plain,(
% 0.22/0.56    spl4_37 <=> sK0 = k2_relat_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.56  fof(f462,plain,(
% 0.22/0.56    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_37),
% 0.22/0.56    inference(superposition,[],[f278,f457])).
% 0.22/0.56  fof(f457,plain,(
% 0.22/0.56    sK0 = k2_relat_1(sK3) | ~spl4_37),
% 0.22/0.56    inference(avatar_component_clause,[],[f455])).
% 0.22/0.56  fof(f278,plain,(
% 0.22/0.56    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(global_subsumption,[],[f252,f114])).
% 0.22/0.56  fof(f114,plain,(
% 0.22/0.56    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.22/0.56  fof(f252,plain,(
% 0.22/0.56    ( ! [X2] : (v5_relat_1(X2,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.56    inference(resolution,[],[f98,f119])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f105])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(flattening,[],[f64])).
% 0.22/0.56  % (27395)Refutation not found, incomplete strategy% (27395)------------------------------
% 0.22/0.56  % (27395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27395)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (27395)Memory used [KB]: 11001
% 0.22/0.56  % (27395)Time elapsed: 0.150 s
% 0.22/0.56  % (27395)------------------------------
% 0.22/0.56  % (27395)------------------------------
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.56  fof(f458,plain,(
% 0.22/0.56    ~spl4_9 | spl4_37 | ~spl4_36),
% 0.22/0.56    inference(avatar_split_clause,[],[f452,f448,f455,f162])).
% 0.22/0.56  fof(f448,plain,(
% 0.22/0.56    spl4_36 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.56  fof(f452,plain,(
% 0.22/0.56    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_36),
% 0.22/0.56    inference(superposition,[],[f450,f96])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.56  fof(f450,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_36),
% 0.22/0.56    inference(avatar_component_clause,[],[f448])).
% 0.22/0.56  fof(f451,plain,(
% 0.22/0.56    ~spl4_2 | ~spl4_4 | ~spl4_9 | ~spl4_1 | ~spl4_3 | ~spl4_8 | spl4_36 | ~spl4_11),
% 0.22/0.56    inference(avatar_split_clause,[],[f441,f172,f448,f157,f133,f123,f162,f138,f128])).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    spl4_11 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.56  fof(f441,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_11),
% 0.22/0.56    inference(resolution,[],[f84,f174])).
% 0.22/0.56  fof(f174,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f172])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f40])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 0.22/0.56  fof(f412,plain,(
% 0.22/0.56    ~spl4_32 | spl4_33 | ~spl4_29),
% 0.22/0.56    inference(avatar_split_clause,[],[f402,f366,f409,f405])).
% 0.22/0.56  fof(f366,plain,(
% 0.22/0.56    spl4_29 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.56  fof(f402,plain,(
% 0.22/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_29),
% 0.22/0.56    inference(resolution,[],[f314,f368])).
% 0.22/0.56  fof(f368,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~spl4_29),
% 0.22/0.56    inference(avatar_component_clause,[],[f366])).
% 0.22/0.56  fof(f314,plain,(
% 0.22/0.56    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.22/0.56    inference(resolution,[],[f82,f111])).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f89,f85])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,axiom,(
% 0.22/0.56    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.56    inference(ennf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.56  fof(f369,plain,(
% 0.22/0.56    ~spl4_1 | ~spl4_8 | ~spl4_2 | ~spl4_9 | spl4_29 | ~spl4_11),
% 0.22/0.56    inference(avatar_split_clause,[],[f364,f172,f366,f162,f128,f157,f123])).
% 0.22/0.56  fof(f364,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_11),
% 0.22/0.56    inference(superposition,[],[f174,f86])).
% 0.22/0.56  fof(f244,plain,(
% 0.22/0.56    spl4_20),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f241])).
% 0.22/0.56  fof(f241,plain,(
% 0.22/0.56    $false | spl4_20),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f94,f237])).
% 0.22/0.56  fof(f237,plain,(
% 0.22/0.56    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_20),
% 0.22/0.56    inference(avatar_component_clause,[],[f235])).
% 0.22/0.56  fof(f235,plain,(
% 0.22/0.56    spl4_20 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.56  fof(f238,plain,(
% 0.22/0.56    ~spl4_20 | spl4_17 | ~spl4_9),
% 0.22/0.56    inference(avatar_split_clause,[],[f198,f162,f215,f235])).
% 0.22/0.56  fof(f198,plain,(
% 0.22/0.56    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_9),
% 0.22/0.56    inference(resolution,[],[f88,f164])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.56  fof(f189,plain,(
% 0.22/0.56    spl4_13 | ~spl4_10),
% 0.22/0.56    inference(avatar_split_clause,[],[f184,f167,f186])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    spl4_13 <=> v2_funct_1(k1_xboole_0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    v2_funct_1(k1_xboole_0) | ~spl4_10),
% 0.22/0.56    inference(superposition,[],[f110,f169])).
% 0.22/0.56  fof(f175,plain,(
% 0.22/0.56    spl4_11),
% 0.22/0.56    inference(avatar_split_clause,[],[f72,f172])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f30,f57,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  % (27391)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.22/0.56    inference(negated_conjecture,[],[f27])).
% 0.22/0.56  fof(f27,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 0.22/0.56  fof(f170,plain,(
% 0.22/0.56    spl4_10),
% 0.22/0.56    inference(avatar_split_clause,[],[f112,f167])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.22/0.56    inference(definition_unfolding,[],[f95,f85])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.56  fof(f165,plain,(
% 0.22/0.56    spl4_9),
% 0.22/0.56    inference(avatar_split_clause,[],[f71,f162])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f58])).
% 0.22/0.56  fof(f160,plain,(
% 0.22/0.56    spl4_8),
% 0.22/0.56    inference(avatar_split_clause,[],[f68,f157])).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f58])).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    ~spl4_5 | ~spl4_6),
% 0.22/0.56    inference(avatar_split_clause,[],[f73,f147,f143])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f58])).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    spl4_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f70,f138])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f58])).
% 0.22/0.56  fof(f136,plain,(
% 0.22/0.56    spl4_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f67,f133])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f58])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    spl4_2),
% 0.22/0.56    inference(avatar_split_clause,[],[f69,f128])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    v1_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f58])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    spl4_1),
% 0.22/0.56    inference(avatar_split_clause,[],[f66,f123])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    v1_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f58])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (27390)------------------------------
% 0.22/0.57  % (27390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (27390)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (27390)Memory used [KB]: 11385
% 0.22/0.57  % (27390)Time elapsed: 0.119 s
% 0.22/0.57  % (27390)------------------------------
% 0.22/0.57  % (27390)------------------------------
% 0.22/0.57  % (27388)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (27366)Success in time 0.204 s
%------------------------------------------------------------------------------
