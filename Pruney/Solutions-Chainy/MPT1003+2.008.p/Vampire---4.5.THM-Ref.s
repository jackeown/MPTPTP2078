%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 108 expanded)
%              Number of leaves         :   13 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  217 ( 384 expanded)
%              Number of equality atoms :   68 ( 139 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f42,f46,f50,f58,f74,f82,f89,f99,f103,f113])).

fof(f113,plain,
    ( ~ spl3_3
    | spl3_6
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl3_3
    | spl3_6
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f111,f93])).

fof(f93,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0))
    | ~ spl3_3
    | spl3_6 ),
    inference(backward_demodulation,[],[f49,f38])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f49,plain,
    ( sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_6
  <=> sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f111,plain,
    ( k1_xboole_0 = k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0))
    | ~ spl3_8
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f105,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ spl3_8
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f104,f98])).

fof(f98,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f104,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(resolution,[],[f102,f57])).

fof(f57,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_8
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f105,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK2) = k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0))
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(resolution,[],[f102,f81])).

fof(f81,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f103,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f94,f44,f37,f101])).

fof(f44,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f94,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f45,f38])).

fof(f45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f99,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f95,f37,f33,f97])).

fof(f33,plain,
    ( spl3_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f95,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f34,f38])).

fof(f34,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f89,plain,
    ( ~ spl3_2
    | spl3_4
    | ~ spl3_5
    | spl3_6
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl3_2
    | spl3_4
    | ~ spl3_5
    | spl3_6
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f87,f49])).

fof(f87,plain,
    ( sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))
    | ~ spl3_2
    | spl3_4
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f86,f85])).

fof(f85,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_2
    | spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f84,f34])).

fof(f84,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f83,f41])).

fof(f41,plain,
    ( k1_xboole_0 != sK1
    | spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f83,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(resolution,[],[f73,f45])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f86,plain,
    ( k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(resolution,[],[f81,f45])).

fof(f82,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f16,f80])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

fof(f74,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f22,f72])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f58,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f23,f56])).

fof(f23,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f14,f48])).

fof(f14,plain,(
    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f13,f44])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f6])).

fof(f42,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f10,f40,f37])).

fof(f10,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f33])).

fof(f12,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (20467)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.46  % (20458)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (20453)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.46  % (20458)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f35,f42,f46,f50,f58,f74,f82,f89,f99,f103,f113])).
% 0.20/0.46  fof(f113,plain,(
% 0.20/0.46    ~spl3_3 | spl3_6 | ~spl3_8 | ~spl3_14 | ~spl3_15 | ~spl3_16),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    $false | (~spl3_3 | spl3_6 | ~spl3_8 | ~spl3_14 | ~spl3_15 | ~spl3_16)),
% 0.20/0.46    inference(subsumption_resolution,[],[f111,f93])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0)) | (~spl3_3 | spl3_6)),
% 0.20/0.46    inference(backward_demodulation,[],[f49,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    k1_xboole_0 = sK0 | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl3_3 <=> k1_xboole_0 = sK0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | spl3_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl3_6 <=> sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    k1_xboole_0 = k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0)) | (~spl3_8 | ~spl3_14 | ~spl3_15 | ~spl3_16)),
% 0.20/0.46    inference(forward_demodulation,[],[f105,f107])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) | (~spl3_8 | ~spl3_15 | ~spl3_16)),
% 0.20/0.46    inference(subsumption_resolution,[],[f104,f98])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl3_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f97])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    spl3_15 <=> v1_funct_2(sK2,k1_xboole_0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK2) | ~v1_funct_2(sK2,k1_xboole_0,sK1) | (~spl3_8 | ~spl3_16)),
% 0.20/0.46    inference(resolution,[],[f102,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) ) | ~spl3_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    spl3_8 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl3_16),
% 0.20/0.46    inference(avatar_component_clause,[],[f101])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    spl3_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.46  fof(f105,plain,(
% 0.20/0.46    k1_relset_1(k1_xboole_0,sK1,sK2) = k8_relset_1(k1_xboole_0,sK1,sK2,k7_relset_1(k1_xboole_0,sK1,sK2,k1_xboole_0)) | (~spl3_14 | ~spl3_16)),
% 0.20/0.46    inference(resolution,[],[f102,f81])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)) ) | ~spl3_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f80])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    spl3_14 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    spl3_16 | ~spl3_3 | ~spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f94,f44,f37,f101])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl3_3 | ~spl3_5)),
% 0.20/0.46    inference(backward_demodulation,[],[f45,f38])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f44])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    spl3_15 | ~spl3_2 | ~spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f95,f37,f33,f97])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl3_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    v1_funct_2(sK2,k1_xboole_0,sK1) | (~spl3_2 | ~spl3_3)),
% 0.20/0.46    inference(backward_demodulation,[],[f34,f38])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    v1_funct_2(sK2,sK0,sK1) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f33])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    ~spl3_2 | spl3_4 | ~spl3_5 | spl3_6 | ~spl3_12 | ~spl3_14),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    $false | (~spl3_2 | spl3_4 | ~spl3_5 | spl3_6 | ~spl3_12 | ~spl3_14)),
% 0.20/0.46    inference(subsumption_resolution,[],[f87,f49])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    sK0 = k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) | (~spl3_2 | spl3_4 | ~spl3_5 | ~spl3_12 | ~spl3_14)),
% 0.20/0.46    inference(forward_demodulation,[],[f86,f85])).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl3_2 | spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.20/0.46    inference(subsumption_resolution,[],[f84,f34])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | (spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.20/0.46    inference(subsumption_resolution,[],[f83,f41])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    k1_xboole_0 != sK1 | spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl3_4 <=> k1_xboole_0 = sK1),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | (~spl3_5 | ~spl3_12)),
% 0.20/0.46    inference(resolution,[],[f73,f45])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) ) | ~spl3_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f72])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    spl3_12 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0)) = k1_relset_1(sK0,sK1,sK2) | (~spl3_5 | ~spl3_14)),
% 0.20/0.46    inference(resolution,[],[f81,f45])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    spl3_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f16,f80])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    spl3_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f72])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(flattening,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    spl3_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f56])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.46    inference(equality_resolution,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ~spl3_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f14,f48])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    sK0 != k8_relset_1(sK0,sK1,sK2,k7_relset_1(sK0,sK1,sK2,sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.46    inference(flattening,[],[f5])).
% 0.20/0.46  fof(f5,plain,(
% 0.20/0.46    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.20/0.46    inference(negated_conjecture,[],[f3])).
% 0.20/0.46  fof(f3,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = X0))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f13,f44])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    spl3_3 | ~spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f10,f40,f37])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f12,f33])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (20458)------------------------------
% 0.20/0.46  % (20458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (20458)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (20458)Memory used [KB]: 10618
% 0.20/0.46  % (20458)Time elapsed: 0.058 s
% 0.20/0.46  % (20458)------------------------------
% 0.20/0.46  % (20458)------------------------------
% 0.20/0.47  % (20448)Success in time 0.111 s
%------------------------------------------------------------------------------
