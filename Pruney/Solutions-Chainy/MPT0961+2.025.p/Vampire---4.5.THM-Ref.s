%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 358 expanded)
%              Number of leaves         :   35 ( 123 expanded)
%              Depth                    :   15
%              Number of atoms          :  437 (1007 expanded)
%              Number of equality atoms :   95 ( 273 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (3832)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f776,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f79,f83,f87,f115,f148,f255,f420,f427,f433,f436,f437,f439,f449,f453,f461,f502,f527,f761])).

fof(f761,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | spl3_30 ),
    inference(avatar_contradiction_clause,[],[f755])).

% (3820)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% (3818)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (3829)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (3829)Refutation not found, incomplete strategy% (3829)------------------------------
% (3829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3829)Termination reason: Refutation not found, incomplete strategy

% (3829)Memory used [KB]: 1663
% (3829)Time elapsed: 0.085 s
% (3829)------------------------------
% (3829)------------------------------
% (3824)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (3828)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (3833)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (3828)Refutation not found, incomplete strategy% (3828)------------------------------
% (3828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3828)Termination reason: Refutation not found, incomplete strategy

% (3828)Memory used [KB]: 6140
% (3828)Time elapsed: 0.087 s
% (3828)------------------------------
% (3828)------------------------------
% (3819)Refutation not found, incomplete strategy% (3819)------------------------------
% (3819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3819)Termination reason: Refutation not found, incomplete strategy

% (3819)Memory used [KB]: 10618
% (3819)Time elapsed: 0.086 s
% (3819)------------------------------
% (3819)------------------------------
fof(f755,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_13
    | spl3_30 ),
    inference(subsumption_resolution,[],[f746,f751])).

fof(f751,plain,
    ( ! [X0,X1] : v1_funct_2(X1,k1_xboole_0,X0)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f554,f598])).

fof(f598,plain,
    ( ! [X0] : m1_subset_1(X0,k1_xboole_0)
    | ~ spl3_12 ),
    inference(superposition,[],[f88,f147])).

fof(f147,plain,
    ( ! [X2] : k1_xboole_0 = X2
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_12
  <=> ! [X2] : k1_xboole_0 = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f43,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f554,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_xboole_0)
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f553,f147])).

fof(f553,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f200,f147])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f198,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f198,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f98,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f98,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f66,f62])).

fof(f66,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f746,plain,
    ( ! [X0] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl3_12
    | ~ spl3_13
    | spl3_30 ),
    inference(forward_demodulation,[],[f745,f248])).

fof(f248,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f745,plain,
    ( ! [X0] : ~ v1_funct_2(sK0,k1_xboole_0,X0)
    | ~ spl3_12
    | spl3_30 ),
    inference(forward_demodulation,[],[f588,f147])).

fof(f588,plain,
    ( ! [X0] : ~ v1_funct_2(sK0,k1_relat_1(sK0),X0)
    | ~ spl3_12
    | spl3_30 ),
    inference(superposition,[],[f448,f147])).

fof(f448,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl3_30
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f527,plain,
    ( ~ spl3_11
    | spl3_33 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | ~ spl3_11
    | spl3_33 ),
    inference(resolution,[],[f492,f203])).

fof(f203,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl3_11 ),
    inference(trivial_inequality_removal,[],[f202])).

fof(f202,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f201,f144])).

fof(f144,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_11
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f201,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f200,f88])).

fof(f492,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl3_33
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f502,plain,
    ( ~ spl3_33
    | ~ spl3_13
    | spl3_31 ),
    inference(avatar_split_clause,[],[f487,f451,f247,f491])).

fof(f451,plain,
    ( spl3_31
  <=> v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f487,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_13
    | spl3_31 ),
    inference(superposition,[],[f452,f248])).

fof(f452,plain,
    ( ~ v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f451])).

fof(f461,plain,(
    ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl3_15 ),
    inference(resolution,[],[f454,f88])).

fof(f454,plain,
    ( ! [X0] : ~ m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(X0))
    | ~ spl3_15 ),
    inference(resolution,[],[f254,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f254,plain,
    ( ! [X0] : ~ r1_tarski(k1_relat_1(sK0),X0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl3_15
  <=> ! [X0] : ~ r1_tarski(k1_relat_1(sK0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f453,plain,
    ( ~ spl3_31
    | spl3_9
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f442,f418,f113,f451])).

fof(f113,plain,
    ( spl3_9
  <=> v1_funct_2(sK0,k1_xboole_0,k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f418,plain,
    ( spl3_27
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f442,plain,
    ( ~ v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)
    | spl3_9
    | ~ spl3_27 ),
    inference(superposition,[],[f114,f419])).

fof(f419,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f418])).

fof(f114,plain,
    ( ~ v1_funct_2(sK0,k1_xboole_0,k2_relat_1(sK0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f449,plain,
    ( ~ spl3_30
    | spl3_2
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f441,f418,f72,f447])).

fof(f72,plain,
    ( spl3_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f441,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl3_2
    | ~ spl3_27 ),
    inference(superposition,[],[f73,f419])).

fof(f73,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f439,plain,
    ( spl3_15
    | ~ spl3_14
    | ~ spl3_4
    | spl3_8 ),
    inference(avatar_split_clause,[],[f320,f110,f81,f250,f253])).

fof(f250,plain,
    ( spl3_14
  <=> v1_xboole_0(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f81,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f110,plain,
    ( spl3_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_relat_1(sK0))
        | ~ r1_tarski(k1_relat_1(sK0),X0) )
    | ~ spl3_4
    | spl3_8 ),
    inference(resolution,[],[f313,f243])).

fof(f243,plain,
    ( ! [X0] :
        ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0))))
        | ~ r1_tarski(k1_relat_1(sK0),X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f242,f88])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(X1))
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k1_relat_1(sK0),X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f241,f49])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(sK0),X0)
        | ~ r1_tarski(k1_relat_1(sK0),X1)
        | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_4 ),
    inference(resolution,[],[f53,f82])).

fof(f82,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f313,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_xboole_0(X1) )
    | spl3_8 ),
    inference(resolution,[],[f111,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f111,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f437,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_relat_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f436,plain,(
    spl3_29 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | spl3_29 ),
    inference(resolution,[],[f432,f88])).

fof(f432,plain,
    ( ~ m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0)))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl3_29
  <=> m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f433,plain,
    ( ~ spl3_29
    | spl3_28 ),
    inference(avatar_split_clause,[],[f428,f425,f431])).

fof(f425,plain,
    ( spl3_28
  <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f428,plain,
    ( ~ m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0)))
    | spl3_28 ),
    inference(resolution,[],[f426,f49])).

fof(f426,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f425])).

fof(f427,plain,
    ( ~ spl3_28
    | spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f422,f81,f75,f425])).

fof(f75,plain,
    ( spl3_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f422,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))
    | spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f76,f243])).

fof(f76,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f420,plain,
    ( ~ spl3_3
    | spl3_27
    | spl3_2 ),
    inference(avatar_split_clause,[],[f416,f72,f418,f75])).

fof(f416,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl3_2 ),
    inference(trivial_inequality_removal,[],[f411])).

fof(f411,plain,
    ( k1_relat_1(sK0) != k1_relat_1(sK0)
    | k1_xboole_0 = k2_relat_1(sK0)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | spl3_2 ),
    inference(resolution,[],[f358,f73])).

fof(f358,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relat_1(X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f57,f54])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f255,plain,
    ( spl3_13
    | ~ spl3_14
    | spl3_15
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f244,f81,f253,f250,f247])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK0),X0)
        | ~ v1_xboole_0(k2_relat_1(sK0))
        | k1_xboole_0 = sK0 )
    | ~ spl3_4 ),
    inference(resolution,[],[f243,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_xboole_0(X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f48,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f47,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f148,plain,
    ( spl3_11
    | spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f141,f85,f146,f143])).

fof(f85,plain,
    ( spl3_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f141,plain,
    ( ! [X2] :
        ( k1_xboole_0 = X2
        | k1_xboole_0 = k1_relat_1(k1_xboole_0) )
    | ~ spl3_5 ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = k1_relat_1(k1_xboole_0) )
    | ~ spl3_5 ),
    inference(superposition,[],[f50,f134])).

fof(f134,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_relat_1(k1_xboole_0))
    | ~ spl3_5 ),
    inference(resolution,[],[f130,f86])).

fof(f86,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f130,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | k1_xboole_0 = k2_zfmisc_1(X1,k1_relat_1(X2)) ) ),
    inference(resolution,[],[f125,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f122,f88])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f115,plain,
    ( ~ spl3_8
    | ~ spl3_9
    | spl3_2 ),
    inference(avatar_split_clause,[],[f106,f72,f113,f110])).

fof(f106,plain,
    ( ~ v1_funct_2(sK0,k1_xboole_0,k2_relat_1(sK0))
    | ~ v1_xboole_0(sK0)
    | spl3_2 ),
    inference(superposition,[],[f73,f104])).

fof(f104,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f102,f44])).

fof(f87,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f41,f85])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f83,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f38,f81])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f79,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f39,f69])).

fof(f69,plain,
    ( spl3_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f75,f72,f69])).

fof(f40,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (3816)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.44  % (3816)Refutation not found, incomplete strategy% (3816)------------------------------
% 0.20/0.44  % (3816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (3816)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (3816)Memory used [KB]: 6140
% 0.20/0.44  % (3816)Time elapsed: 0.032 s
% 0.20/0.44  % (3816)------------------------------
% 0.20/0.44  % (3816)------------------------------
% 0.20/0.44  % (3826)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.45  % (3831)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (3826)Refutation not found, incomplete strategy% (3826)------------------------------
% 0.20/0.46  % (3826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (3826)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (3826)Memory used [KB]: 6140
% 0.20/0.46  % (3826)Time elapsed: 0.057 s
% 0.20/0.46  % (3826)------------------------------
% 0.20/0.46  % (3826)------------------------------
% 0.20/0.46  % (3831)Refutation not found, incomplete strategy% (3831)------------------------------
% 0.20/0.46  % (3831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (3831)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (3831)Memory used [KB]: 6140
% 0.20/0.46  % (3831)Time elapsed: 0.058 s
% 0.20/0.46  % (3831)------------------------------
% 0.20/0.46  % (3831)------------------------------
% 0.20/0.46  % (3830)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (3823)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (3822)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (3819)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (3822)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  % (3832)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  fof(f776,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f77,f79,f83,f87,f115,f148,f255,f420,f427,f433,f436,f437,f439,f449,f453,f461,f502,f527,f761])).
% 0.20/0.48  fof(f761,plain,(
% 0.20/0.48    ~spl3_12 | ~spl3_13 | spl3_30),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f755])).
% 0.20/0.48  % (3820)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (3818)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (3829)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (3829)Refutation not found, incomplete strategy% (3829)------------------------------
% 0.20/0.48  % (3829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (3829)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (3829)Memory used [KB]: 1663
% 0.20/0.48  % (3829)Time elapsed: 0.085 s
% 0.20/0.48  % (3829)------------------------------
% 0.20/0.48  % (3829)------------------------------
% 0.20/0.49  % (3824)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (3828)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (3833)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.49  % (3828)Refutation not found, incomplete strategy% (3828)------------------------------
% 0.20/0.49  % (3828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3828)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (3828)Memory used [KB]: 6140
% 0.20/0.49  % (3828)Time elapsed: 0.087 s
% 0.20/0.49  % (3828)------------------------------
% 0.20/0.49  % (3828)------------------------------
% 0.20/0.49  % (3819)Refutation not found, incomplete strategy% (3819)------------------------------
% 0.20/0.49  % (3819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3819)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (3819)Memory used [KB]: 10618
% 0.20/0.49  % (3819)Time elapsed: 0.086 s
% 0.20/0.49  % (3819)------------------------------
% 0.20/0.49  % (3819)------------------------------
% 0.20/0.49  fof(f755,plain,(
% 0.20/0.49    $false | (~spl3_12 | ~spl3_13 | spl3_30)),
% 0.20/0.49    inference(subsumption_resolution,[],[f746,f751])).
% 0.20/0.49  fof(f751,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_funct_2(X1,k1_xboole_0,X0)) ) | ~spl3_12),
% 0.20/0.49    inference(subsumption_resolution,[],[f554,f598])).
% 0.20/0.49  fof(f598,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(X0,k1_xboole_0)) ) | ~spl3_12),
% 0.20/0.49    inference(superposition,[],[f88,f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ( ! [X2] : (k1_xboole_0 = X2) ) | ~spl3_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f146])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    spl3_12 <=> ! [X2] : k1_xboole_0 = X2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f43,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.49  fof(f554,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_xboole_0) | v1_funct_2(X1,k1_xboole_0,X0)) ) | ~spl3_12),
% 0.20/0.49    inference(forward_demodulation,[],[f553,f147])).
% 0.20/0.49  fof(f553,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) ) | ~spl3_12),
% 0.20/0.49    inference(subsumption_resolution,[],[f200,f147])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f199])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f198,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.20/0.49    inference(superposition,[],[f98,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f66,f62])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.20/0.49    inference(equality_resolution,[],[f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f746,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl3_12 | ~spl3_13 | spl3_30)),
% 0.20/0.49    inference(forward_demodulation,[],[f745,f248])).
% 0.20/0.49  fof(f248,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | ~spl3_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f247])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    spl3_13 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.49  fof(f745,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(sK0,k1_xboole_0,X0)) ) | (~spl3_12 | spl3_30)),
% 0.20/0.49    inference(forward_demodulation,[],[f588,f147])).
% 0.20/0.49  fof(f588,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_funct_2(sK0,k1_relat_1(sK0),X0)) ) | (~spl3_12 | spl3_30)),
% 0.20/0.49    inference(superposition,[],[f448,f147])).
% 0.20/0.49  fof(f448,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | spl3_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f447])).
% 0.20/0.49  fof(f447,plain,(
% 0.20/0.49    spl3_30 <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.49  fof(f527,plain,(
% 0.20/0.49    ~spl3_11 | spl3_33),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f524])).
% 0.20/0.49  fof(f524,plain,(
% 0.20/0.49    $false | (~spl3_11 | spl3_33)),
% 0.20/0.49    inference(resolution,[],[f492,f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl3_11),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f202])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl3_11),
% 0.20/0.49    inference(forward_demodulation,[],[f201,f144])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    spl3_11 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.20/0.49    inference(resolution,[],[f200,f88])).
% 0.20/0.49  fof(f492,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl3_33),
% 0.20/0.49    inference(avatar_component_clause,[],[f491])).
% 0.20/0.49  fof(f491,plain,(
% 0.20/0.49    spl3_33 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.49  fof(f502,plain,(
% 0.20/0.49    ~spl3_33 | ~spl3_13 | spl3_31),
% 0.20/0.49    inference(avatar_split_clause,[],[f487,f451,f247,f491])).
% 0.20/0.49  fof(f451,plain,(
% 0.20/0.49    spl3_31 <=> v1_funct_2(sK0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.49  fof(f487,plain,(
% 0.20/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_13 | spl3_31)),
% 0.20/0.49    inference(superposition,[],[f452,f248])).
% 0.20/0.49  fof(f452,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) | spl3_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f451])).
% 0.20/0.49  fof(f461,plain,(
% 0.20/0.49    ~spl3_15),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f459])).
% 0.20/0.49  fof(f459,plain,(
% 0.20/0.49    $false | ~spl3_15),
% 0.20/0.49    inference(resolution,[],[f454,f88])).
% 0.20/0.49  fof(f454,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(X0))) ) | ~spl3_15),
% 0.20/0.49    inference(resolution,[],[f254,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.20/0.49    inference(unused_predicate_definition_removal,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.49  fof(f254,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0)) ) | ~spl3_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f253])).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    spl3_15 <=> ! [X0] : ~r1_tarski(k1_relat_1(sK0),X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f453,plain,(
% 0.20/0.49    ~spl3_31 | spl3_9 | ~spl3_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f442,f418,f113,f451])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    spl3_9 <=> v1_funct_2(sK0,k1_xboole_0,k2_relat_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f418,plain,(
% 0.20/0.49    spl3_27 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.49  fof(f442,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_xboole_0,k1_xboole_0) | (spl3_9 | ~spl3_27)),
% 0.20/0.49    inference(superposition,[],[f114,f419])).
% 0.20/0.49  fof(f419,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(sK0) | ~spl3_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f418])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_xboole_0,k2_relat_1(sK0)) | spl3_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f113])).
% 0.20/0.49  fof(f449,plain,(
% 0.20/0.49    ~spl3_30 | spl3_2 | ~spl3_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f441,f418,f72,f447])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f441,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl3_2 | ~spl3_27)),
% 0.20/0.49    inference(superposition,[],[f73,f419])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f439,plain,(
% 0.20/0.49    spl3_15 | ~spl3_14 | ~spl3_4 | spl3_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f320,f110,f81,f250,f253])).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    spl3_14 <=> v1_xboole_0(k2_relat_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    spl3_4 <=> v1_relat_1(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    spl3_8 <=> v1_xboole_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f320,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(k2_relat_1(sK0)) | ~r1_tarski(k1_relat_1(sK0),X0)) ) | (~spl3_4 | spl3_8)),
% 0.20/0.49    inference(resolution,[],[f313,f243])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK0)))) | ~r1_tarski(k1_relat_1(sK0),X0)) ) | ~spl3_4),
% 0.20/0.49    inference(resolution,[],[f242,f88])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(k2_relat_1(sK0),k1_zfmisc_1(X1)) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(sK0),X0)) ) | ~spl3_4),
% 0.20/0.49    inference(resolution,[],[f241,f49])).
% 0.20/0.49  fof(f241,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X1) | m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_4),
% 0.20/0.49    inference(resolution,[],[f53,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    v1_relat_1(sK0) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f81])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.49  fof(f313,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X1)) ) | spl3_8),
% 0.20/0.49    inference(resolution,[],[f111,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0) | spl3_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f110])).
% 0.20/0.49  fof(f437,plain,(
% 0.20/0.49    k1_xboole_0 != k2_relat_1(sK0) | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_relat_1(sK0))),
% 0.20/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.49  fof(f436,plain,(
% 0.20/0.49    spl3_29),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f434])).
% 0.20/0.49  fof(f434,plain,(
% 0.20/0.49    $false | spl3_29),
% 0.20/0.49    inference(resolution,[],[f432,f88])).
% 0.20/0.49  fof(f432,plain,(
% 0.20/0.49    ~m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0))) | spl3_29),
% 0.20/0.49    inference(avatar_component_clause,[],[f431])).
% 0.20/0.49  fof(f431,plain,(
% 0.20/0.49    spl3_29 <=> m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.49  fof(f433,plain,(
% 0.20/0.49    ~spl3_29 | spl3_28),
% 0.20/0.49    inference(avatar_split_clause,[],[f428,f425,f431])).
% 0.20/0.49  fof(f425,plain,(
% 0.20/0.49    spl3_28 <=> r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.49  fof(f428,plain,(
% 0.20/0.49    ~m1_subset_1(k1_relat_1(sK0),k1_zfmisc_1(k1_relat_1(sK0))) | spl3_28),
% 0.20/0.49    inference(resolution,[],[f426,f49])).
% 0.20/0.49  fof(f426,plain,(
% 0.20/0.49    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | spl3_28),
% 0.20/0.49    inference(avatar_component_clause,[],[f425])).
% 0.20/0.49  fof(f427,plain,(
% 0.20/0.49    ~spl3_28 | spl3_3 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f422,f81,f75,f425])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    spl3_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f422,plain,(
% 0.20/0.49    ~r1_tarski(k1_relat_1(sK0),k1_relat_1(sK0)) | (spl3_3 | ~spl3_4)),
% 0.20/0.49    inference(resolution,[],[f76,f243])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f75])).
% 0.20/0.49  fof(f420,plain,(
% 0.20/0.49    ~spl3_3 | spl3_27 | spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f416,f72,f418,f75])).
% 0.20/0.49  fof(f416,plain,(
% 0.20/0.49    k1_xboole_0 = k2_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl3_2),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f411])).
% 0.20/0.49  fof(f411,plain,(
% 0.20/0.49    k1_relat_1(sK0) != k1_relat_1(sK0) | k1_xboole_0 = k2_relat_1(sK0) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | spl3_2),
% 0.20/0.49    inference(resolution,[],[f358,f73])).
% 0.20/0.49  fof(f358,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relat_1(X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f355])).
% 0.20/0.49  fof(f355,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(superposition,[],[f57,f54])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    spl3_13 | ~spl3_14 | spl3_15 | ~spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f244,f81,f253,f250,f247])).
% 0.20/0.49  fof(f244,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | ~v1_xboole_0(k2_relat_1(sK0)) | k1_xboole_0 = sK0) ) | ~spl3_4),
% 0.20/0.49    inference(resolution,[],[f243,f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_xboole_0(X2) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(resolution,[],[f48,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(resolution,[],[f47,f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.49    inference(rectify,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    spl3_11 | spl3_12 | ~spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f141,f85,f146,f143])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    spl3_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X2] : (k1_xboole_0 = X2 | k1_xboole_0 = k1_relat_1(k1_xboole_0)) ) | ~spl3_5),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f140])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X2] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X2 | k1_xboole_0 = k1_relat_1(k1_xboole_0)) ) | ~spl3_5),
% 0.20/0.49    inference(superposition,[],[f50,f134])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_relat_1(k1_xboole_0))) ) | ~spl3_5),
% 0.20/0.49    inference(resolution,[],[f130,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0) | ~spl3_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f85])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v1_xboole_0(X2) | k1_xboole_0 = k2_zfmisc_1(X1,k1_relat_1(X2))) )),
% 0.20/0.49    inference(resolution,[],[f125,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.20/0.49    inference(resolution,[],[f122,f88])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ~spl3_8 | ~spl3_9 | spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f106,f72,f113,f110])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ~v1_funct_2(sK0,k1_xboole_0,k2_relat_1(sK0)) | ~v1_xboole_0(sK0) | spl3_2),
% 0.20/0.49    inference(superposition,[],[f73,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f102,f44])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    spl3_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f85])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl3_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f38,f81])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    v1_relat_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f39,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl3_1 <=> v1_funct_1(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    v1_funct_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f75,f72,f69])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (3822)------------------------------
% 0.20/0.49  % (3822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3822)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (3822)Memory used [KB]: 11001
% 0.20/0.49  % (3822)Time elapsed: 0.042 s
% 0.20/0.49  % (3822)------------------------------
% 0.20/0.49  % (3822)------------------------------
% 0.20/0.49  % (3825)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (3815)Success in time 0.141 s
%------------------------------------------------------------------------------
