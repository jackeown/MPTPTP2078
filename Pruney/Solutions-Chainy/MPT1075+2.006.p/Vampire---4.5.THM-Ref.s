%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  246 ( 509 expanded)
%              Number of leaves         :   50 ( 213 expanded)
%              Depth                    :   14
%              Number of atoms          : 1054 (1973 expanded)
%              Number of equality atoms :  112 ( 176 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f598,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f101,f122,f128,f133,f146,f151,f166,f171,f186,f212,f216,f228,f229,f251,f263,f280,f294,f319,f436,f443,f447,f453,f495,f516,f541,f578,f596,f597])).

fof(f597,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5)
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f596,plain,
    ( spl6_61
    | spl6_3
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_47
    | ~ spl6_55
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f591,f568,f538,f450,f316,f291,f93,f83,f593])).

fof(f593,plain,
    ( spl6_61
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f83,plain,
    ( spl6_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f93,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f291,plain,
    ( spl6_27
  <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f316,plain,
    ( spl6_29
  <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f450,plain,
    ( spl6_47
  <=> k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f538,plain,
    ( spl6_55
  <=> k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f568,plain,
    ( spl6_60
  <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f591,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_3
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_47
    | ~ spl6_55
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f590,f540])).

fof(f540,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f538])).

fof(f590,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | spl6_3
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_47
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f589,f452])).

fof(f452,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f450])).

fof(f589,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_3
    | ~ spl6_5
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_60 ),
    inference(resolution,[],[f588,f95])).

fof(f95,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f588,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | spl6_3
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f551,f569])).

fof(f569,plain,
    ( v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f568])).

fof(f551,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | spl6_3
    | ~ spl6_27
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f550,f85])).

fof(f85,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f550,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_27
    | ~ spl6_29 ),
    inference(resolution,[],[f300,f318])).

fof(f318,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f316])).

fof(f300,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X8,X9)
        | v1_xboole_0(X8)
        | ~ m1_subset_1(X10,X8)
        | k3_funct_2(X8,X9,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X10) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X10) )
    | ~ spl6_27 ),
    inference(resolution,[],[f293,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

% (4543)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f293,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f291])).

fof(f578,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_60 ),
    inference(avatar_contradiction_clause,[],[f577])).

fof(f577,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_60 ),
    inference(subsumption_resolution,[],[f576,f121])).

% (4555)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f121,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f576,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8
    | ~ spl6_9
    | spl6_60 ),
    inference(subsumption_resolution,[],[f575,f127])).

fof(f127,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f575,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_9
    | spl6_60 ),
    inference(subsumption_resolution,[],[f574,f75])).

fof(f75,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f574,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_2
    | ~ spl6_9
    | spl6_60 ),
    inference(subsumption_resolution,[],[f572,f132])).

fof(f132,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f572,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_2
    | spl6_60 ),
    inference(resolution,[],[f570,f114])).

fof(f114,plain,
    ( ! [X17,X15,X18,X16] :
        ( v1_funct_2(k8_funct_2(X15,X16,X18,sK3,X17),X15,X18)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X18)))
        | ~ v1_funct_2(sK3,X15,X16) )
    | ~ spl6_2 ),
    inference(resolution,[],[f80,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f80,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f570,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | spl6_60 ),
    inference(avatar_component_clause,[],[f568])).

fof(f541,plain,
    ( spl6_55
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f523,f512,f272,f260,f125,f88,f73,f538])).

fof(f88,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f260,plain,
    ( spl6_24
  <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f272,plain,
    ( spl6_26
  <=> v1_funct_2(sK4,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f512,plain,
    ( spl6_53
  <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f523,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f522,f90])).

fof(f90,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f522,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_24
    | ~ spl6_26
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f521,f262])).

fof(f262,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f260])).

fof(f521,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f520,f127])).

fof(f520,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_26
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f517,f273])).

fof(f273,plain,
    ( v1_funct_2(sK4,sK0,sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f272])).

fof(f517,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ v1_funct_2(sK4,sK0,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_1
    | ~ spl6_53 ),
    inference(superposition,[],[f514,f105])).

fof(f105,plain,
    ( ! [X10,X8,X9] :
        ( k3_funct_2(X8,X9,sK4,X10) = k1_funct_1(sK4,X10)
        | ~ v1_funct_2(sK4,X8,X9)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ m1_subset_1(X10,X8)
        | v1_xboole_0(X8) )
    | ~ spl6_1 ),
    inference(resolution,[],[f75,f67])).

fof(f514,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f512])).

fof(f516,plain,
    ( spl6_53
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_22
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f423,f272,f248,f225,f130,f125,f119,f93,f88,f83,f78,f73,f512])).

fof(f225,plain,
    ( spl6_22
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f248,plain,
    ( spl6_23
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f423,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_22
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f422,f250])).

fof(f250,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f248])).

fof(f422,plain,
    ( k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_22
    | ~ spl6_26 ),
    inference(resolution,[],[f311,f95])).

% (4547)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f311,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_22
    | ~ spl6_26 ),
    inference(resolution,[],[f305,f241])).

fof(f241,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f240,f85])).

fof(f240,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f239,f121])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f111,f132])).

fof(f111,plain,
    ( ! [X6,X7,X5] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(sK3,X5,X6)
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X7,X5)
        | m1_subset_1(k3_funct_2(X5,X6,sK3,X7),X6) )
    | ~ spl6_2 ),
    inference(resolution,[],[f80,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f305,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | spl6_22
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f258,f273])).

fof(f258,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,sK0,sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | spl6_22 ),
    inference(subsumption_resolution,[],[f257,f227])).

fof(f227,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f225])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,sK0,sK2)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f256,f90])).

fof(f256,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0) )
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(resolution,[],[f102,f127])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK4,X1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X2,X1)
        | k3_funct_2(X1,X0,sK4,X2) = k7_partfun1(X0,sK4,X2) )
    | ~ spl6_1 ),
    inference(resolution,[],[f75,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).

fof(f495,plain,
    ( spl6_3
    | ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f494])).

fof(f494,plain,
    ( $false
    | spl6_3
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f471,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f471,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3
    | ~ spl6_30 ),
    inference(superposition,[],[f85,f328])).

fof(f328,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl6_30
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f453,plain,
    ( spl6_47
    | ~ spl6_5
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f448,f430,f93,f450])).

fof(f430,plain,
    ( spl6_44
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f448,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ spl6_5
    | ~ spl6_44 ),
    inference(resolution,[],[f431,f95])).

fof(f431,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f430])).

fof(f447,plain,
    ( ~ spl6_9
    | spl6_46 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl6_9
    | spl6_46 ),
    inference(subsumption_resolution,[],[f445,f54])).

% (4555)Refutation not found, incomplete strategy% (4555)------------------------------
% (4555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4544)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f445,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl6_9
    | spl6_46 ),
    inference(resolution,[],[f444,f132])).

fof(f444,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_46 ),
    inference(resolution,[],[f442,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f442,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_46 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl6_46
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f443,plain,
    ( ~ spl6_46
    | ~ spl6_14
    | spl6_45 ),
    inference(avatar_split_clause,[],[f438,f433,f163,f440])).

fof(f163,plain,
    ( spl6_14
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f433,plain,
    ( spl6_45
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f438,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl6_14
    | spl6_45 ),
    inference(subsumption_resolution,[],[f437,f165])).

fof(f165,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f437,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | spl6_45 ),
    inference(resolution,[],[f435,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f435,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl6_45 ),
    inference(avatar_component_clause,[],[f433])).

fof(f436,plain,
    ( spl6_44
    | ~ spl6_45
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_21
    | spl6_30 ),
    inference(avatar_split_clause,[],[f342,f326,f218,f183,f130,f125,f119,f88,f78,f73,f433,f430])).

fof(f183,plain,
    ( spl6_18
  <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f218,plain,
    ( spl6_21
  <=> sK0 = k1_relset_1(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f342,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f341,f327])).

fof(f327,plain,
    ( k1_xboole_0 != sK1
    | spl6_30 ),
    inference(avatar_component_clause,[],[f326])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f340,f132])).

fof(f340,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f339,f121])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f338,f80])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ m1_subset_1(X0,sK1)
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(superposition,[],[f235,f185])).

fof(f185,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f235,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(X2,X0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | spl6_4
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f234,f90])).

fof(f234,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f233,f127])).

fof(f233,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_1
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f232,f75])).

fof(f232,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,sK0,X1),sK0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK0)
        | k1_xboole_0 = X0
        | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2)) )
    | ~ spl6_21 ),
    inference(superposition,[],[f60,f220])).

fof(f220,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f218])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X5,X1)
      | v1_xboole_0(X2)
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f319,plain,
    ( spl6_29
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f314,f130,f125,f119,f78,f73,f316])).

fof(f314,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f313,f75])).

fof(f313,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f282,f127])).

fof(f282,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0)
        | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f281,f121])).

fof(f281,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f115,f132])).

fof(f115,plain,
    ( ! [X21,X19,X22,X20] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_2(sK3,X19,X20)
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X20,X22)))
        | m1_subset_1(k8_funct_2(X19,X20,X22,sK3,X21),k1_zfmisc_1(k2_zfmisc_1(X19,X22))) )
    | ~ spl6_2 ),
    inference(resolution,[],[f80,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f294,plain,
    ( spl6_27
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f289,f130,f125,f119,f78,f73,f291])).

fof(f289,plain,
    ( v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f288,f75])).

fof(f288,plain,
    ( ~ v1_funct_1(sK4)
    | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(resolution,[],[f253,f127])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | ~ v1_funct_1(X0)
        | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0)) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f252,f121])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
        | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0)) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f113,f132])).

fof(f113,plain,
    ( ! [X14,X12,X13,X11] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_2(sK3,X11,X12)
        | ~ v1_funct_1(X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X14)))
        | v1_funct_1(k8_funct_2(X11,X12,X14,sK3,X13)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f80,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f280,plain,
    ( ~ spl6_1
    | ~ spl6_8
    | ~ spl6_21
    | spl6_26 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_21
    | spl6_26 ),
    inference(subsumption_resolution,[],[f278,f127])).

fof(f278,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_1
    | ~ spl6_21
    | spl6_26 ),
    inference(subsumption_resolution,[],[f277,f220])).

fof(f277,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_1
    | spl6_26 ),
    inference(resolution,[],[f274,f103])).

fof(f103,plain,
    ( ! [X4,X3] :
        ( v1_funct_2(sK4,X3,X4)
        | k1_relset_1(X3,X4,sK4) != X3
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl6_1 ),
    inference(resolution,[],[f75,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

% (4555)Termination reason: Refutation not found, incomplete strategy

% (4555)Memory used [KB]: 10618
% (4555)Time elapsed: 0.052 s
% (4555)------------------------------
% (4555)------------------------------
fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).

fof(f274,plain,
    ( ~ v1_funct_2(sK4,sK0,sK2)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f272])).

fof(f263,plain,
    ( spl6_24
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f255,f248,f130,f119,f93,f83,f78,f260])).

fof(f255,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f254,f95])).

fof(f254,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ m1_subset_1(sK5,sK1)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_23 ),
    inference(superposition,[],[f241,f250])).

fof(f251,plain,
    ( spl6_23
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f245,f130,f119,f93,f83,f78,f248])).

fof(f245,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f244,f95])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | spl6_3
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f243,f85])).

fof(f243,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f242,f121])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_2
    | ~ spl6_9 ),
    inference(resolution,[],[f112,f132])).

fof(f112,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_2(sK3,X8,X9)
        | v1_xboole_0(X8)
        | ~ m1_subset_1(X10,X8)
        | k3_funct_2(X8,X9,sK3,X10) = k1_funct_1(sK3,X10) )
    | ~ spl6_2 ),
    inference(resolution,[],[f80,f67])).

fof(f229,plain,
    ( sK0 != k1_relat_1(sK4)
    | k1_relat_1(sK4) != k1_relset_1(sK0,sK2,sK4)
    | sK0 = k1_relset_1(sK0,sK2,sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f228,plain,
    ( ~ spl6_22
    | spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f223,f125,f98,f88,f225])).

fof(f98,plain,
    ( spl6_6
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f223,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f222,f127])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_xboole_0(X0) )
    | spl6_4
    | ~ spl6_6 ),
    inference(resolution,[],[f117,f100])).

fof(f100,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ v1_xboole_0(X0) )
    | spl6_4 ),
    inference(resolution,[],[f90,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f216,plain,
    ( ~ spl6_8
    | spl6_19 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl6_8
    | spl6_19 ),
    inference(subsumption_resolution,[],[f214,f54])).

fof(f214,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | ~ spl6_8
    | spl6_19 ),
    inference(resolution,[],[f213,f127])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_19 ),
    inference(resolution,[],[f207,f53])).

fof(f207,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl6_19
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f212,plain,
    ( ~ spl6_19
    | spl6_20
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f203,f148,f98,f209,f205])).

fof(f209,plain,
    ( spl6_20
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f148,plain,
    ( spl6_11
  <=> v4_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f203,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f123,f150])).

fof(f150,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f148])).

fof(f123,plain,
    ( ~ v4_relat_1(sK4,sK0)
    | sK0 = k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl6_6 ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f186,plain,
    ( spl6_18
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f141,f130,f183])).

fof(f141,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)
    | ~ spl6_9 ),
    inference(resolution,[],[f132,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f171,plain,
    ( spl6_15
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f136,f125,f168])).

fof(f168,plain,
    ( spl6_15
  <=> k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f136,plain,
    ( k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4)
    | ~ spl6_8 ),
    inference(resolution,[],[f127,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f166,plain,
    ( spl6_14
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f139,f130,f163])).

fof(f139,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f132,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f151,plain,
    ( spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f134,f125,f148])).

fof(f134,plain,
    ( v4_relat_1(sK4,sK0)
    | ~ spl6_8 ),
    inference(resolution,[],[f127,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f146,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f43,f143])).

fof(f143,plain,
    ( spl6_10
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f43,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

fof(f133,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f48,f130])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f128,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f45,f125])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f122,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f47,f119])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f101,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f42,f98])).

fof(f42,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f41,f93])).

fof(f41,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f50,f88])).

fof(f50,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f49,f83])).

fof(f49,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f46,f78])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f76,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f44,f73])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (4540)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (4537)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (4550)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (4546)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (4549)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (4541)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (4537)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (4538)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (4536)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (4539)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f598,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f101,f122,f128,f133,f146,f151,f166,f171,f186,f212,f216,f228,f229,f251,f263,f280,f294,f319,f436,f443,f447,f453,f495,f516,f541,f578,f596,f597])).
% 0.21/0.49  fof(f597,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK0,sK3,sK5) != k1_funct_1(sK3,sK5) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f596,plain,(
% 0.21/0.49    spl6_61 | spl6_3 | ~spl6_5 | ~spl6_27 | ~spl6_29 | ~spl6_47 | ~spl6_55 | ~spl6_60),
% 0.21/0.49    inference(avatar_split_clause,[],[f591,f568,f538,f450,f316,f291,f93,f83,f593])).
% 0.21/0.49  fof(f593,plain,(
% 0.21/0.49    spl6_61 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl6_3 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    spl6_27 <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    spl6_29 <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.49  fof(f450,plain,(
% 0.21/0.49    spl6_47 <=> k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.21/0.49  fof(f538,plain,(
% 0.21/0.49    spl6_55 <=> k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.21/0.49  fof(f568,plain,(
% 0.21/0.49    spl6_60 <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 0.21/0.49  fof(f591,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_3 | ~spl6_5 | ~spl6_27 | ~spl6_29 | ~spl6_47 | ~spl6_55 | ~spl6_60)),
% 0.21/0.49    inference(forward_demodulation,[],[f590,f540])).
% 0.21/0.49  fof(f540,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl6_55),
% 0.21/0.49    inference(avatar_component_clause,[],[f538])).
% 0.21/0.49  fof(f590,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (spl6_3 | ~spl6_5 | ~spl6_27 | ~spl6_29 | ~spl6_47 | ~spl6_60)),
% 0.21/0.49    inference(forward_demodulation,[],[f589,f452])).
% 0.21/0.49  fof(f452,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~spl6_47),
% 0.21/0.49    inference(avatar_component_clause,[],[f450])).
% 0.21/0.49  fof(f589,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (spl6_3 | ~spl6_5 | ~spl6_27 | ~spl6_29 | ~spl6_60)),
% 0.21/0.49    inference(resolution,[],[f588,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    m1_subset_1(sK5,sK1) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f588,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (spl6_3 | ~spl6_27 | ~spl6_29 | ~spl6_60)),
% 0.21/0.49    inference(subsumption_resolution,[],[f551,f569])).
% 0.21/0.49  fof(f569,plain,(
% 0.21/0.49    v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~spl6_60),
% 0.21/0.49    inference(avatar_component_clause,[],[f568])).
% 0.21/0.49  fof(f551,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (spl6_3 | ~spl6_27 | ~spl6_29)),
% 0.21/0.49    inference(subsumption_resolution,[],[f550,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1) | spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f550,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | (~spl6_27 | ~spl6_29)),
% 0.21/0.49    inference(resolution,[],[f300,f318])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f316])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    ( ! [X10,X8,X9] : (~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X8,X9) | v1_xboole_0(X8) | ~m1_subset_1(X10,X8) | k3_funct_2(X8,X9,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X10) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X10)) ) | ~spl6_27),
% 0.21/0.49    inference(resolution,[],[f293,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f37])).
% 0.21/0.49  % (4543)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | ~spl6_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f291])).
% 0.21/0.49  fof(f578,plain,(
% 0.21/0.49    ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_60),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f577])).
% 0.21/0.49  fof(f577,plain,(
% 0.21/0.49    $false | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_60)),
% 0.21/0.49    inference(subsumption_resolution,[],[f576,f121])).
% 0.21/0.49  % (4555)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK0) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f576,plain,(
% 0.21/0.49    ~v1_funct_2(sK3,sK1,sK0) | (~spl6_1 | ~spl6_2 | ~spl6_8 | ~spl6_9 | spl6_60)),
% 0.21/0.49    inference(subsumption_resolution,[],[f575,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f575,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_1 | ~spl6_2 | ~spl6_9 | spl6_60)),
% 0.21/0.49    inference(subsumption_resolution,[],[f574,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    v1_funct_1(sK4) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl6_1 <=> v1_funct_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f574,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_2 | ~spl6_9 | spl6_60)),
% 0.21/0.49    inference(subsumption_resolution,[],[f572,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl6_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f572,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_2 | spl6_60)),
% 0.21/0.49    inference(resolution,[],[f570,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X17,X15,X18,X16] : (v1_funct_2(k8_funct_2(X15,X16,X18,sK3,X17),X15,X18) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) | ~v1_funct_1(X17) | ~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X18))) | ~v1_funct_2(sK3,X15,X16)) ) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f80,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    v1_funct_1(sK3) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl6_2 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f570,plain,(
% 0.21/0.49    ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | spl6_60),
% 0.21/0.49    inference(avatar_component_clause,[],[f568])).
% 0.21/0.49  fof(f541,plain,(
% 0.21/0.49    spl6_55 | ~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_24 | ~spl6_26 | ~spl6_53),
% 0.21/0.49    inference(avatar_split_clause,[],[f523,f512,f272,f260,f125,f88,f73,f538])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl6_4 <=> v1_xboole_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    spl6_24 <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    spl6_26 <=> v1_funct_2(sK4,sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.49  fof(f512,plain,(
% 0.21/0.49    spl6_53 <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.21/0.49  fof(f523,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_24 | ~spl6_26 | ~spl6_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f522,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0) | spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f522,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | v1_xboole_0(sK0) | (~spl6_1 | ~spl6_8 | ~spl6_24 | ~spl6_26 | ~spl6_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f521,f262])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~spl6_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f260])).
% 0.21/0.49  fof(f521,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | v1_xboole_0(sK0) | (~spl6_1 | ~spl6_8 | ~spl6_26 | ~spl6_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f520,f127])).
% 0.21/0.49  fof(f520,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | v1_xboole_0(sK0) | (~spl6_1 | ~spl6_26 | ~spl6_53)),
% 0.21/0.49    inference(subsumption_resolution,[],[f517,f273])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    v1_funct_2(sK4,sK0,sK2) | ~spl6_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f272])).
% 0.21/0.49  fof(f517,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~v1_funct_2(sK4,sK0,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | v1_xboole_0(sK0) | (~spl6_1 | ~spl6_53)),
% 0.21/0.49    inference(superposition,[],[f514,f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X10,X8,X9] : (k3_funct_2(X8,X9,sK4,X10) = k1_funct_1(sK4,X10) | ~v1_funct_2(sK4,X8,X9) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~m1_subset_1(X10,X8) | v1_xboole_0(X8)) ) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f75,f67])).
% 0.21/0.49  fof(f514,plain,(
% 0.21/0.49    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~spl6_53),
% 0.21/0.49    inference(avatar_component_clause,[],[f512])).
% 0.21/0.49  fof(f516,plain,(
% 0.21/0.49    spl6_53 | ~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_22 | ~spl6_23 | ~spl6_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f423,f272,f248,f225,f130,f125,f119,f93,f88,f83,f78,f73,f512])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    spl6_22 <=> v1_xboole_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    spl6_23 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_22 | ~spl6_23 | ~spl6_26)),
% 0.21/0.49    inference(forward_demodulation,[],[f422,f250])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | ~spl6_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f248])).
% 0.21/0.49  fof(f422,plain,(
% 0.21/0.49    k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_22 | ~spl6_26)),
% 0.21/0.49    inference(resolution,[],[f311,f95])).
% 0.21/0.49  % (4547)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_3 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_22 | ~spl6_26)),
% 0.21/0.49    inference(resolution,[],[f305,f241])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) | ~m1_subset_1(X0,sK1)) ) | (~spl6_2 | spl6_3 | ~spl6_7 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f240,f85])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f239,f121])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.49    inference(resolution,[],[f111,f132])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X6,X7,X5] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(sK3,X5,X6) | v1_xboole_0(X5) | ~m1_subset_1(X7,X5) | m1_subset_1(k3_funct_2(X5,X6,sK3,X7),X6)) ) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f80,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | spl6_4 | ~spl6_8 | spl6_22 | ~spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f258,f273])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | spl6_4 | ~spl6_8 | spl6_22)),
% 0.21/0.49    inference(subsumption_resolution,[],[f257,f227])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2) | spl6_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f225])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | spl6_4 | ~spl6_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f256,f90])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(sK0) | ~v1_funct_2(sK4,sK0,sK2) | v1_xboole_0(sK2) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k7_partfun1(sK2,sK4,X0)) ) | (~spl6_1 | ~spl6_8)),
% 0.21/0.49    inference(resolution,[],[f102,f127])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X1) | ~v1_funct_2(sK4,X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,X1) | k3_funct_2(X1,X0,sK4,X2) = k7_partfun1(X0,sK4,X2)) ) | ~spl6_1),
% 0.21/0.49    inference(resolution,[],[f75,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_2)).
% 0.21/0.49  fof(f495,plain,(
% 0.21/0.49    spl6_3 | ~spl6_30),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f494])).
% 0.21/0.49  fof(f494,plain,(
% 0.21/0.49    $false | (spl6_3 | ~spl6_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f471,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f471,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | (spl6_3 | ~spl6_30)),
% 0.21/0.49    inference(superposition,[],[f85,f328])).
% 0.21/0.49  fof(f328,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f326])).
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    spl6_30 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.49  fof(f453,plain,(
% 0.21/0.49    spl6_47 | ~spl6_5 | ~spl6_44),
% 0.21/0.49    inference(avatar_split_clause,[],[f448,f430,f93,f450])).
% 0.21/0.49  fof(f430,plain,(
% 0.21/0.49    spl6_44 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.49  fof(f448,plain,(
% 0.21/0.49    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (~spl6_5 | ~spl6_44)),
% 0.21/0.49    inference(resolution,[],[f431,f95])).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))) ) | ~spl6_44),
% 0.21/0.49    inference(avatar_component_clause,[],[f430])).
% 0.21/0.49  fof(f447,plain,(
% 0.21/0.49    ~spl6_9 | spl6_46),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f446])).
% 0.21/0.49  fof(f446,plain,(
% 0.21/0.49    $false | (~spl6_9 | spl6_46)),
% 0.21/0.49    inference(subsumption_resolution,[],[f445,f54])).
% 0.21/0.49  % (4555)Refutation not found, incomplete strategy% (4555)------------------------------
% 0.21/0.49  % (4555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4544)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f445,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | (~spl6_9 | spl6_46)),
% 0.21/0.49    inference(resolution,[],[f444,f132])).
% 0.21/0.49  fof(f444,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_46),
% 0.21/0.49    inference(resolution,[],[f442,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f442,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | spl6_46),
% 0.21/0.49    inference(avatar_component_clause,[],[f440])).
% 0.21/0.49  fof(f440,plain,(
% 0.21/0.49    spl6_46 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.49  fof(f443,plain,(
% 0.21/0.49    ~spl6_46 | ~spl6_14 | spl6_45),
% 0.21/0.49    inference(avatar_split_clause,[],[f438,f433,f163,f440])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl6_14 <=> v5_relat_1(sK3,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.49  fof(f433,plain,(
% 0.21/0.49    spl6_45 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.21/0.49  fof(f438,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | (~spl6_14 | spl6_45)),
% 0.21/0.49    inference(subsumption_resolution,[],[f437,f165])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    v5_relat_1(sK3,sK0) | ~spl6_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f163])).
% 0.21/0.49  fof(f437,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | ~v5_relat_1(sK3,sK0) | spl6_45),
% 0.21/0.49    inference(resolution,[],[f435,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.49  fof(f435,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK3),sK0) | spl6_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f433])).
% 0.21/0.49  fof(f436,plain,(
% 0.21/0.49    spl6_44 | ~spl6_45 | ~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_18 | ~spl6_21 | spl6_30),
% 0.21/0.49    inference(avatar_split_clause,[],[f342,f326,f218,f183,f130,f125,f119,f88,f78,f73,f433,f430])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    spl6_18 <=> k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl6_21 <=> sK0 = k1_relset_1(sK0,sK2,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.49  fof(f342,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_18 | ~spl6_21 | spl6_30)),
% 0.21/0.49    inference(subsumption_resolution,[],[f341,f327])).
% 0.21/0.49  fof(f327,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f326])).
% 0.21/0.49  fof(f341,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_18 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f340,f132])).
% 0.21/0.49  fof(f340,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_18 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f339,f121])).
% 0.21/0.49  fof(f339,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | ~spl6_2 | spl6_4 | ~spl6_8 | ~spl6_18 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f338,f80])).
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(X0,sK1) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,X0))) ) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_18 | ~spl6_21)),
% 0.21/0.49    inference(superposition,[],[f235,f185])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f183])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(X2,X0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | spl6_4 | ~spl6_8 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f234,f90])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(X2,X0) | v1_xboole_0(sK0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | ~spl6_8 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f233,f127])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X2,X0) | v1_xboole_0(sK0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))) ) | (~spl6_1 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f232,f75])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,sK0,X1),sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X2,X0) | v1_xboole_0(sK0) | k1_xboole_0 = X0 | k1_funct_1(k8_funct_2(X0,sK0,sK2,X1,sK4),X2) = k7_partfun1(sK2,sK4,k1_funct_1(X1,X2))) ) | ~spl6_21),
% 0.21/0.49    inference(superposition,[],[f60,f220])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK2,sK4) | ~spl6_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f218])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X5,X1) | v1_xboole_0(X2) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    spl6_29 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f314,f130,f125,f119,f78,f73,f316])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f313,f75])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.49    inference(resolution,[],[f282,f127])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f281,f121])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | m1_subset_1(k8_funct_2(sK1,sK0,X1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.49    inference(resolution,[],[f115,f132])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X21,X19,X22,X20] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) | ~v1_funct_2(sK3,X19,X20) | ~v1_funct_1(X21) | ~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X20,X22))) | m1_subset_1(k8_funct_2(X19,X20,X22,sK3,X21),k1_zfmisc_1(k2_zfmisc_1(X19,X22)))) ) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f80,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    spl6_27 | ~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f289,f130,f125,f119,f78,f73,f291])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_1 | ~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f288,f75])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    ~v1_funct_1(sK4) | v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | (~spl6_2 | ~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.49    inference(resolution,[],[f253,f127])).
% 0.21/0.49  fof(f253,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | ~v1_funct_1(X0) | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0))) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f252,f121])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) | v1_funct_1(k8_funct_2(sK1,sK0,X1,sK3,X0))) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.49    inference(resolution,[],[f113,f132])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    ( ! [X14,X12,X13,X11] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_2(sK3,X11,X12) | ~v1_funct_1(X13) | ~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X12,X14))) | v1_funct_1(k8_funct_2(X11,X12,X14,sK3,X13))) ) | ~spl6_2),
% 0.21/0.49    inference(resolution,[],[f80,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ~spl6_1 | ~spl6_8 | ~spl6_21 | spl6_26),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f279])).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    $false | (~spl6_1 | ~spl6_8 | ~spl6_21 | spl6_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f278,f127])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl6_1 | ~spl6_21 | spl6_26)),
% 0.21/0.50    inference(subsumption_resolution,[],[f277,f220])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl6_1 | spl6_26)),
% 0.21/0.50    inference(resolution,[],[f274,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X4,X3] : (v1_funct_2(sK4,X3,X4) | k1_relset_1(X3,X4,sK4) != X3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f75,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  % (4555)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4555)Memory used [KB]: 10618
% 0.21/0.50  % (4555)Time elapsed: 0.052 s
% 0.21/0.50  % (4555)------------------------------
% 0.21/0.50  % (4555)------------------------------
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_funct_2)).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ~v1_funct_2(sK4,sK0,sK2) | spl6_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f272])).
% 0.21/0.50  fof(f263,plain,(
% 0.21/0.50    spl6_24 | ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f255,f248,f130,f119,f93,f83,f78,f260])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9 | ~spl6_23)),
% 0.21/0.50    inference(subsumption_resolution,[],[f254,f95])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~m1_subset_1(sK5,sK1) | (~spl6_2 | spl6_3 | ~spl6_7 | ~spl6_9 | ~spl6_23)),
% 0.21/0.50    inference(superposition,[],[f241,f250])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    spl6_23 | ~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f245,f130,f119,f93,f83,f78,f248])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | (~spl6_2 | spl6_3 | ~spl6_5 | ~spl6_7 | ~spl6_9)),
% 0.21/0.50    inference(resolution,[],[f244,f95])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl6_2 | spl6_3 | ~spl6_7 | ~spl6_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f243,f85])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl6_2 | ~spl6_7 | ~spl6_9)),
% 0.21/0.50    inference(subsumption_resolution,[],[f242,f121])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK0) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl6_2 | ~spl6_9)),
% 0.21/0.50    inference(resolution,[],[f112,f132])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(sK3,X8,X9) | v1_xboole_0(X8) | ~m1_subset_1(X10,X8) | k3_funct_2(X8,X9,sK3,X10) = k1_funct_1(sK3,X10)) ) | ~spl6_2),
% 0.21/0.50    inference(resolution,[],[f80,f67])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    sK0 != k1_relat_1(sK4) | k1_relat_1(sK4) != k1_relset_1(sK0,sK2,sK4) | sK0 = k1_relset_1(sK0,sK2,sK4)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ~spl6_22 | spl6_4 | ~spl6_6 | ~spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f223,f125,f98,f88,f225])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl6_6 <=> v1_partfun1(sK4,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ~v1_xboole_0(sK2) | (spl6_4 | ~spl6_6 | ~spl6_8)),
% 0.21/0.50    inference(resolution,[],[f222,f127])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_xboole_0(X0)) ) | (spl6_4 | ~spl6_6)),
% 0.21/0.50    inference(resolution,[],[f117,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    v1_partfun1(sK4,sK0) | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_partfun1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~v1_xboole_0(X0)) ) | spl6_4),
% 0.21/0.50    inference(resolution,[],[f90,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    ~spl6_8 | spl6_19),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f215])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    $false | (~spl6_8 | spl6_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f214,f54])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | (~spl6_8 | spl6_19)),
% 0.21/0.50    inference(resolution,[],[f213,f127])).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_19),
% 0.21/0.50    inference(resolution,[],[f207,f53])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ~v1_relat_1(sK4) | spl6_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f205])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    spl6_19 <=> v1_relat_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    ~spl6_19 | spl6_20 | ~spl6_6 | ~spl6_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f203,f148,f98,f209,f205])).
% 0.21/0.50  fof(f209,plain,(
% 0.21/0.50    spl6_20 <=> sK0 = k1_relat_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    spl6_11 <=> v4_relat_1(sK4,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | (~spl6_6 | ~spl6_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f123,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    v4_relat_1(sK4,sK0) | ~spl6_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f148])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ~v4_relat_1(sK4,sK0) | sK0 = k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl6_6),
% 0.21/0.50    inference(resolution,[],[f100,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    spl6_18 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f141,f130,f183])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) | ~spl6_9),
% 0.21/0.50    inference(resolution,[],[f132,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    spl6_15 | ~spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f136,f125,f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl6_15 <=> k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    k1_relat_1(sK4) = k1_relset_1(sK0,sK2,sK4) | ~spl6_8),
% 0.21/0.50    inference(resolution,[],[f127,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl6_14 | ~spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f139,f130,f163])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    v5_relat_1(sK3,sK0) | ~spl6_9),
% 0.21/0.50    inference(resolution,[],[f132,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    spl6_11 | ~spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f134,f125,f148])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    v4_relat_1(sK4,sK0) | ~spl6_8),
% 0.21/0.50    inference(resolution,[],[f127,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ~spl6_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl6_10 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f16])).
% 0.21/0.50  fof(f16,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl6_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f130])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl6_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f125])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f119])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f98])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    v1_partfun1(sK4,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f93])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    m1_subset_1(sK5,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ~spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f88])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f83])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f78])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f44,f73])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    v1_funct_1(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (4537)------------------------------
% 0.21/0.50  % (4537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4537)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (4537)Memory used [KB]: 11001
% 0.21/0.50  % (4537)Time elapsed: 0.084 s
% 0.21/0.50  % (4537)------------------------------
% 0.21/0.50  % (4537)------------------------------
% 0.21/0.50  % (4530)Success in time 0.14 s
%------------------------------------------------------------------------------
