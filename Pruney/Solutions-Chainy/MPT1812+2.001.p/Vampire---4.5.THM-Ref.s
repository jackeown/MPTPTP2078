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
% DateTime   : Thu Dec  3 13:19:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----WARNING: Could not form TPTP format derivation
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (26900)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.46  % (26893)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.46  % (26900)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (26908)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f318,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f142,f144,f148,f152,f156,f160,f164,f168,f172,f176,f178,f180,f224,f233,f257,f277,f292,f295,f298,f301,f304,f308,f311,f314,f317])).
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    spl7_11 | ~spl7_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f316])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    $false | (spl7_11 | ~spl7_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f315,f222])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    sP1(sK3,sK5,sK6,sK4,sK2) | ~spl7_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f221])).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    spl7_14 <=> sP1(sK3,sK5,sK6,sK4,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.47  fof(f315,plain,(
% 0.21/0.47    ~sP1(sK3,sK5,sK6,sK4,sK2) | spl7_11),
% 0.21/0.47    inference(resolution,[],[f137,f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : ((sP1(X0,X1,X2,X3,X4) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) & ((m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) & m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) & v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) | ~sP1(X0,X1,X2,X3,X4)))),
% 0.21/0.47    inference(rectify,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X1,X3,X4,X2,X0] : ((sP1(X1,X3,X4,X2,X0) | (~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | ~sP1(X1,X3,X4,X2,X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f12])).
% 0.21/0.47  % (26904)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X1,X3,X4,X2,X0] : (sP1(X1,X3,X4,X2,X0) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | spl7_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f135])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl7_11 <=> v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.47  fof(f314,plain,(
% 0.21/0.47    spl7_9 | ~spl7_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f313])).
% 0.21/0.47  fof(f313,plain,(
% 0.21/0.47    $false | (spl7_9 | ~spl7_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f312,f222])).
% 0.21/0.47  fof(f312,plain,(
% 0.21/0.47    ~sP1(sK3,sK5,sK6,sK4,sK2) | spl7_9),
% 0.21/0.47    inference(resolution,[],[f129,f81])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | spl7_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl7_9 <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.47  fof(f311,plain,(
% 0.21/0.47    spl7_6 | ~spl7_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f310])).
% 0.21/0.47  fof(f310,plain,(
% 0.21/0.47    $false | (spl7_6 | ~spl7_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f309,f222])).
% 0.21/0.47  fof(f309,plain,(
% 0.21/0.47    ~sP1(sK3,sK5,sK6,sK4,sK2) | spl7_6),
% 0.21/0.47    inference(resolution,[],[f117,f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | spl7_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f115])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl7_6 <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.47  fof(f308,plain,(
% 0.21/0.47    spl7_12 | ~spl7_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f307])).
% 0.21/0.47  fof(f307,plain,(
% 0.21/0.47    $false | (spl7_12 | ~spl7_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f306,f222])).
% 0.21/0.47  fof(f306,plain,(
% 0.21/0.47    ~sP1(sK3,sK5,sK6,sK4,sK2) | spl7_12),
% 0.21/0.47    inference(resolution,[],[f141,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl7_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f139])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    spl7_12 <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.47  fof(f304,plain,(
% 0.21/0.47    spl7_7 | ~spl7_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f303])).
% 0.21/0.47  fof(f303,plain,(
% 0.21/0.47    $false | (spl7_7 | ~spl7_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f302,f222])).
% 0.21/0.47  fof(f302,plain,(
% 0.21/0.47    ~sP1(sK3,sK5,sK6,sK4,sK2) | spl7_7),
% 0.21/0.47    inference(resolution,[],[f121,f79])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | spl7_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl7_7 <=> v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.47  fof(f301,plain,(
% 0.21/0.47    spl7_8 | ~spl7_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f300])).
% 0.21/0.47  fof(f300,plain,(
% 0.21/0.47    $false | (spl7_8 | ~spl7_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f299,f222])).
% 0.21/0.47  fof(f299,plain,(
% 0.21/0.47    ~sP1(sK3,sK5,sK6,sK4,sK2) | spl7_8),
% 0.21/0.47    inference(resolution,[],[f125,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | spl7_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f123])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    spl7_8 <=> m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.47  fof(f298,plain,(
% 0.21/0.47    spl7_5 | ~spl7_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f297])).
% 0.21/0.47  fof(f297,plain,(
% 0.21/0.47    $false | (spl7_5 | ~spl7_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f296,f222])).
% 0.21/0.47  fof(f296,plain,(
% 0.21/0.47    ~sP1(sK3,sK5,sK6,sK4,sK2) | spl7_5),
% 0.21/0.47    inference(resolution,[],[f113,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2)) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | spl7_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl7_5 <=> v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.47  fof(f295,plain,(
% 0.21/0.47    spl7_10 | ~spl7_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f294])).
% 0.21/0.47  fof(f294,plain,(
% 0.21/0.47    $false | (spl7_10 | ~spl7_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f293,f222])).
% 0.21/0.47  fof(f293,plain,(
% 0.21/0.47    ~sP1(sK3,sK5,sK6,sK4,sK2) | spl7_10),
% 0.21/0.47    inference(resolution,[],[f133,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~sP1(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | spl7_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f131])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    spl7_10 <=> v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.47  fof(f292,plain,(
% 0.21/0.47    spl7_14 | ~spl7_10 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f291,f139,f135,f127,f123,f119,f115,f111,f131,f221])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | sP1(sK3,sK5,sK6,sK4,sK2) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f290,f112])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | ~spl7_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f111])).
% 0.21/0.47  fof(f290,plain,(
% 0.21/0.47    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | sP1(sK3,sK5,sK6,sK4,sK2) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | (~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f289,f116])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~spl7_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f115])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | sP1(sK3,sK5,sK6,sK4,sK2) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f258,f120])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~spl7_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f258,plain,(
% 0.21/0.47    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | sP1(sK3,sK5,sK6,sK4,sK2) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | (~spl7_8 | ~spl7_9 | ~spl7_11 | ~spl7_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f240,f128])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | ~spl7_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f127])).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | sP1(sK3,sK5,sK6,sK4,sK2) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | (~spl7_8 | ~spl7_11 | ~spl7_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f239,f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | ~spl7_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f135])).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | sP1(sK3,sK5,sK6,sK4,sK2) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | (~spl7_8 | ~spl7_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f234,f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl7_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f139])).
% 0.21/0.47  fof(f234,plain,(
% 0.21/0.47    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | sP1(sK3,sK5,sK6,sK4,sK2) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | ~spl7_8),
% 0.21/0.47    inference(resolution,[],[f85,f124])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~spl7_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f123])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~m1_subset_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),X1,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X1,X2)) | sP1(X0,X1,X2,X3,X4) | ~v5_pre_topc(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),X3,X0) | ~v1_funct_2(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2),u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(k3_tmap_1(X4,X0,k1_tsep_1(X4,X3,X1),X3,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f277,plain,(
% 0.21/0.47    ~spl7_13 | spl7_14 | ~spl7_15),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f276])).
% 0.21/0.47  fof(f276,plain,(
% 0.21/0.47    $false | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f275,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ~v2_struct_0(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    (((((~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(sK6)) & ((m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))) | (m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(sK6))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & v1_tsep_1(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f15,f20,f19,f18,f17,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmis% (26908)Refutation not found, incomplete strategy% (26908)------------------------------
% 0.21/0.47  % (26908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  c_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(sK2,X1,k1_tsep_1(sK2,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),X3,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),X2,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) & v5_pre_topc(X4,k1_tsep_1(sK2,X2,X3),sK3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,X2,X3)),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & v1_tsep_1(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4)) & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & v1_tsep_1(sK4,sK2) & ~v2_struct_0(sK4))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) | ~v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),X3,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),X3,X4)) & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),sK4,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,X3),sK4,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,X3),sK3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,X3)),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & v1_tsep_1(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4)) & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK2) & v1_tsep_1(sK5,sK2) & ~v2_struct_0(sK5))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X4] : ((~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),sK5,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,X4)) & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),sK4,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4),u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v5_pre_topc(X4,k1_tsep_1(sK2,sK4,sK5),sK3) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(X4)) => ((~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(sK6)) & ((m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) & m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) & v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) & v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) & v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6))) | (m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(sK6))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) | ~m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) | ~v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) & ((m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))) | (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <~> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <~> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_tsep_1(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_tmap_1)).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f274,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v2_pre_topc(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f273,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    l1_pre_topc(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f272,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~v2_struct_0(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f272,plain,(
% 0.21/0.47    v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f271,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    v2_pre_topc(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f270,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    l1_pre_topc(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f270,plain,(
% 0.21/0.47    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f269,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~v2_struct_0(sK4)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f269,plain,(
% 0.21/0.47    v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f268,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    m1_pre_topc(sK4,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f268,plain,(
% 0.21/0.47    ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f267,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~v2_struct_0(sK5)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f267,plain,(
% 0.21/0.47    v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f266,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    m1_pre_topc(sK5,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f266,plain,(
% 0.21/0.47    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (~spl7_13 | spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f265,f218])).
% 0.21/0.47  fof(f218,plain,(
% 0.21/0.47    r4_tsep_1(sK2,sK4,sK5) | ~spl7_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f217])).
% 0.21/0.47  fof(f217,plain,(
% 0.21/0.47    spl7_13 <=> r4_tsep_1(sK2,sK4,sK5)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | (spl7_14 | ~spl7_15)),
% 0.21/0.47    inference(subsumption_resolution,[],[f263,f223])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    ~sP1(sK3,sK5,sK6,sK4,sK2) | spl7_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f221])).
% 0.21/0.47  fof(f263,plain,(
% 0.21/0.47    sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~spl7_15),
% 0.21/0.47    inference(resolution,[],[f256,f196])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~sP0(X1,X3,X2,X0,X4) | sP1(X1,X3,X4,X2,X0) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f195,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) & v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) & v1_funct_1(X4)) | ~sP0(X0,X1,X2,X3,X4)))),
% 0.21/0.47    inference(rectify,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X1,X3,X2,X0,X4] : ((sP0(X1,X3,X2,X0,X4) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) & ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) | ~sP0(X1,X3,X2,X0,X4)))),
% 0.21/0.47    inference(nnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X1,X3,X2,X0,X4] : (sP0(X1,X3,X2,X0,X4) <=> (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)))),
% 0.21/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (sP1(X1,X3,X4,X2,X0) | ~sP0(X1,X3,X2,X0,X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f194,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f194,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (sP1(X1,X3,X4,X2,X0) | ~sP0(X1,X3,X2,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f91,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | v1_funct_1(X4)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (sP1(X1,X3,X4,X2,X0) | ~sP0(X1,X3,X2,X0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((sP0(X1,X3,X2,X0,X4) | ~sP1(X1,X3,X4,X2,X0)) & (sP1(X1,X3,X4,X2,X0) | ~sP0(X1,X3,X2,X0,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((sP0(X1,X3,X2,X0,X4) <=> sP1(X1,X3,X4,X2,X0)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(definition_folding,[],[f8,f12,f11])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(X4,k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) <=> (m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),X3,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)) & m1_subset_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),X2,X1) & v1_funct_2(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4))))))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    sP0(sK3,sK5,sK4,sK2,sK6) | ~spl7_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f254])).
% 0.21/0.47  fof(f254,plain,(
% 0.21/0.47    spl7_15 <=> sP0(sK3,sK5,sK4,sK2,sK6)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.47  fof(f257,plain,(
% 0.21/0.47    ~spl7_3 | spl7_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f252,f254,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl7_3 <=> v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.47  % (26908)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  fof(f252,plain,(
% 0.21/0.47    sP0(sK3,sK5,sK4,sK2,sK6) | ~v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f251,f41])).
% 0.21/0.47  
% 0.21/0.47  % (26908)Memory used [KB]: 895
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v1_funct_1(sK6)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % (26908)Time elapsed: 0.058 s
% 0.21/0.48  % (26908)------------------------------
% 0.21/0.48  % (26908)------------------------------
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    sP0(sK3,sK5,sK4,sK2,sK6) | ~v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_1(sK6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f182,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    sP0(sK3,sK5,sK4,sK2,sK6) | ~v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(sK6)),
% 0.21/0.48    inference(resolution,[],[f90,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)))) | sP0(X0,X1,X2,X3,X4) | ~v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X3,X2,X1)),u1_struct_0(X0)) | ~v1_funct_1(X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    spl7_13),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f232])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    $false | spl7_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f231,f29])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    v2_struct_0(sK2) | spl7_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f230,f30])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f229,f31])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f228,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v1_tsep_1(sK4,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    ~v1_tsep_1(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f227,f37])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~m1_pre_topc(sK4,sK2) | ~v1_tsep_1(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f226,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v1_tsep_1(sK5,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~v1_tsep_1(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | ~v1_tsep_1(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_13),
% 0.21/0.48    inference(subsumption_resolution,[],[f225,f40])).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ~m1_pre_topc(sK5,sK2) | ~v1_tsep_1(sK5,sK2) | ~m1_pre_topc(sK4,sK2) | ~v1_tsep_1(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_13),
% 0.21/0.48    inference(resolution,[],[f219,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | ~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r4_tsep_1(X0,X1,X2) | (~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0))) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) => r4_tsep_1(X0,X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tsep_1)).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    ~r4_tsep_1(sK2,sK4,sK5) | spl7_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f217])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    ~spl7_13 | ~spl7_14 | spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f215,f103,f221,f217])).
% 0.21/0.48  % (26896)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f214,f29])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f213,f30])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f212,f31])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f211,f32])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f210,f33])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f209,f34])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f208,f35])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f207,f37])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f206,f38])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f205,f40])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f204,f41])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~v1_funct_1(sK6) | ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f203,f42])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f199,f181])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ~sP0(sK3,sK5,sK4,sK2,sK6) | spl7_3),
% 0.21/0.48    inference(resolution,[],[f88,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ~v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) | spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (v5_pre_topc(X4,k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3,X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ~sP1(sK3,sK5,sK6,sK4,sK2) | sP0(sK3,sK5,sK4,sK2,sK6) | ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~r4_tsep_1(sK2,sK4,sK5) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~m1_pre_topc(sK4,sK2) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.21/0.48    inference(resolution,[],[f92,f43])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~sP1(X1,X3,X4,X2,X0) | sP0(X1,X3,X2,X0,X4) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    spl7_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f179])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    $false | spl7_4),
% 0.21/0.48    inference(subsumption_resolution,[],[f109,f43])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    spl7_4 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl7_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f177])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    $false | spl7_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f42])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl7_2 <=> v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl7_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f175])).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    $false | spl7_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f97,f41])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ~v1_funct_1(sK6) | spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl7_1 <=> v1_funct_1(sK6)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl7_3 | spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f111,f103])).
% 0.21/0.48  % (26907)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    spl7_3 | spl7_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f50,f115,f103])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    spl7_3 | spl7_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f119,f103])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    spl7_3 | spl7_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f58,f123,f103])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl7_3 | spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f62,f127,f103])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl7_3 | spl7_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f66,f131,f103])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl7_3 | spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f70,f135,f103])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl7_3 | spl7_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f74,f139,f103])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f76,f139,f135,f131,f127,f123,f119,f115,f111,f107,f103,f99,f95])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),sK5,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK5,sK6)) | ~m1_subset_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK3)))) | ~v5_pre_topc(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),sK4,sK3) | ~v1_funct_2(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6),u1_struct_0(sK4),u1_struct_0(sK3)) | ~v1_funct_1(k3_tmap_1(sK2,sK3,k1_tsep_1(sK2,sK4,sK5),sK4,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)))) | ~v5_pre_topc(sK6,k1_tsep_1(sK2,sK4,sK5),sK3) | ~v1_funct_2(sK6,u1_struct_0(k1_tsep_1(sK2,sK4,sK5)),u1_struct_0(sK3)) | ~v1_funct_1(sK6)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (26900)------------------------------
% 0.21/0.48  % (26900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (26900)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (26900)Memory used [KB]: 5756
% 0.21/0.48  % (26900)Time elapsed: 0.059 s
% 0.21/0.48  % (26900)------------------------------
% 0.21/0.48  % (26900)------------------------------
% 0.21/0.48  % (26909)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.21/0.48  % (26892)Success in time 0.118 s
%------------------------------------------------------------------------------
