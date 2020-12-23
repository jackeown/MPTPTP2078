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
% DateTime   : Thu Dec  3 13:13:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 199 expanded)
%              Number of leaves         :   28 (  92 expanded)
%              Depth                    :    8
%              Number of atoms          :  352 ( 644 expanded)
%              Number of equality atoms :   83 ( 171 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f60,f68,f72,f76,f80,f85,f102,f109,f138,f146,f151,f158,f167,f198,f203,f210,f221])).

fof(f221,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(subsumption_resolution,[],[f217,f36])).

fof(f36,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_1
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f217,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_30 ),
    inference(superposition,[],[f39,f209])).

fof(f209,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl2_30
  <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f39,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl2_2
  <=> k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f210,plain,
    ( spl2_30
    | ~ spl2_16
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f205,f196,f155,f127,f106,f207])).

fof(f106,plain,
    ( spl2_16
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f127,plain,
    ( spl2_20
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f155,plain,
    ( spl2_24
  <=> sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f196,plain,
    ( spl2_29
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f205,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_16
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f204,f108])).

fof(f108,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f106])).

fof(f204,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ spl2_20
    | ~ spl2_24
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f200,f157])).

fof(f157,plain,
    ( sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f155])).

fof(f200,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_20
    | ~ spl2_29 ),
    inference(resolution,[],[f197,f128])).

fof(f128,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f127])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f196])).

fof(f203,plain,
    ( spl2_2
    | ~ spl2_4
    | ~ spl2_25
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f202,f196,f164,f48,f38])).

fof(f48,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f164,plain,
    ( spl2_25
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f202,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_25
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f199,f166])).

fof(f166,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f164])).

fof(f199,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_29 ),
    inference(resolution,[],[f197,f50])).

fof(f50,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f198,plain,
    ( spl2_29
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f194,f58,f53,f196])).

fof(f53,plain,
    ( spl2_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f58,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(resolution,[],[f59,f55])).

fof(f55,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f167,plain,
    ( spl2_25
    | ~ spl2_22
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f159,f155,f143,f164])).

fof(f143,plain,
    ( spl2_22
  <=> k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f159,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_22
    | ~ spl2_24 ),
    inference(superposition,[],[f145,f157])).

fof(f145,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f143])).

fof(f158,plain,
    ( spl2_24
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f153,f149,f48,f43,f155])).

fof(f43,plain,
    ( spl2_3
  <=> v6_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f149,plain,
    ( spl2_23
  <=> ! [X0] :
        ( ~ v6_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f153,plain,
    ( sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f152,f50])).

fof(f152,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(resolution,[],[f150,f45])).

fof(f45,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ v6_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl2_23
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f147,f66,f53,f149])).

fof(f66,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
        | ~ v6_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v6_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0 )
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f67,f55])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v6_tops_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f146,plain,
    ( spl2_22
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f140,f127,f83,f143])).

fof(f83,plain,
    ( spl2_12
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f140,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(resolution,[],[f128,f84])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f138,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | ~ spl2_9
    | spl2_20 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_9
    | spl2_20 ),
    inference(subsumption_resolution,[],[f136,f55])).

fof(f136,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_9
    | spl2_20 ),
    inference(subsumption_resolution,[],[f135,f50])).

fof(f135,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_9
    | spl2_20 ),
    inference(resolution,[],[f129,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f129,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f127])).

fof(f109,plain,
    ( spl2_16
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f103,f100,f48,f106])).

fof(f100,plain,
    ( spl2_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f103,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(resolution,[],[f101,f50])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f98,f78,f53,f100])).

fof(f78,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) )
    | ~ spl2_5
    | ~ spl2_11 ),
    inference(resolution,[],[f79,f55])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f85,plain,
    ( spl2_12
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f81,f74,f53,f83])).

fof(f74,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)) )
    | ~ spl2_5
    | ~ spl2_10 ),
    inference(resolution,[],[f75,f55])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f74])).

fof(f80,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f31,f78])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f76,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f30,f74])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f72,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f68,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f60,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f56,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1) )
    & v6_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
            & v6_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k2_tops_1(sK0,X1) )
          & v6_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k2_tops_1(sK0,X1) )
        & v6_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1) )
      & v6_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
             => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
                & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
           => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tops_1)).

fof(f51,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f32,f38,f34])).

fof(f32,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1)
    | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(inner_rewriting,[],[f25])).

fof(f25,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:12:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (14447)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (14447)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f222,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f60,f68,f72,f76,f80,f85,f102,f109,f138,f146,f151,f158,f167,f198,f203,f210,f221])).
% 0.22/0.43  fof(f221,plain,(
% 0.22/0.43    spl2_1 | ~spl2_2 | ~spl2_30),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f220])).
% 0.22/0.43  fof(f220,plain,(
% 0.22/0.43    $false | (spl2_1 | ~spl2_2 | ~spl2_30)),
% 0.22/0.43    inference(subsumption_resolution,[],[f217,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1) | spl2_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    spl2_1 <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.43  fof(f217,plain,(
% 0.22/0.43    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) | (~spl2_2 | ~spl2_30)),
% 0.22/0.43    inference(superposition,[],[f39,f209])).
% 0.22/0.43  fof(f209,plain,(
% 0.22/0.43    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_30),
% 0.22/0.43    inference(avatar_component_clause,[],[f207])).
% 0.22/0.43  fof(f207,plain,(
% 0.22/0.43    spl2_30 <=> k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | ~spl2_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f38])).
% 0.22/0.43  fof(f38,plain,(
% 0.22/0.43    spl2_2 <=> k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.43  fof(f210,plain,(
% 0.22/0.43    spl2_30 | ~spl2_16 | ~spl2_20 | ~spl2_24 | ~spl2_29),
% 0.22/0.43    inference(avatar_split_clause,[],[f205,f196,f155,f127,f106,f207])).
% 0.22/0.43  fof(f106,plain,(
% 0.22/0.43    spl2_16 <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.43  fof(f127,plain,(
% 0.22/0.43    spl2_20 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.43  fof(f155,plain,(
% 0.22/0.43    spl2_24 <=> sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.43  fof(f196,plain,(
% 0.22/0.43    spl2_29 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.22/0.43  fof(f205,plain,(
% 0.22/0.43    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | (~spl2_16 | ~spl2_20 | ~spl2_24 | ~spl2_29)),
% 0.22/0.43    inference(forward_demodulation,[],[f204,f108])).
% 0.22/0.43  fof(f108,plain,(
% 0.22/0.43    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) | ~spl2_16),
% 0.22/0.43    inference(avatar_component_clause,[],[f106])).
% 0.22/0.43  fof(f204,plain,(
% 0.22/0.43    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),sK1) | (~spl2_20 | ~spl2_24 | ~spl2_29)),
% 0.22/0.43    inference(forward_demodulation,[],[f200,f157])).
% 0.22/0.43  fof(f157,plain,(
% 0.22/0.43    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~spl2_24),
% 0.22/0.43    inference(avatar_component_clause,[],[f155])).
% 0.22/0.43  fof(f200,plain,(
% 0.22/0.43    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | (~spl2_20 | ~spl2_29)),
% 0.22/0.43    inference(resolution,[],[f197,f128])).
% 0.22/0.43  fof(f128,plain,(
% 0.22/0.43    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_20),
% 0.22/0.43    inference(avatar_component_clause,[],[f127])).
% 0.22/0.43  fof(f197,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_29),
% 0.22/0.43    inference(avatar_component_clause,[],[f196])).
% 0.22/0.43  fof(f203,plain,(
% 0.22/0.43    spl2_2 | ~spl2_4 | ~spl2_25 | ~spl2_29),
% 0.22/0.43    inference(avatar_split_clause,[],[f202,f196,f164,f48,f38])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.43  fof(f164,plain,(
% 0.22/0.43    spl2_25 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.43  fof(f202,plain,(
% 0.22/0.43    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_tops_1(sK0,sK1) | (~spl2_4 | ~spl2_25 | ~spl2_29)),
% 0.22/0.43    inference(forward_demodulation,[],[f199,f166])).
% 0.22/0.43  fof(f166,plain,(
% 0.22/0.43    sK1 = k1_tops_1(sK0,sK1) | ~spl2_25),
% 0.22/0.43    inference(avatar_component_clause,[],[f164])).
% 0.22/0.43  fof(f199,plain,(
% 0.22/0.43    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_29)),
% 0.22/0.43    inference(resolution,[],[f197,f50])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f48])).
% 0.22/0.43  fof(f198,plain,(
% 0.22/0.43    spl2_29 | ~spl2_5 | ~spl2_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f194,f58,f53,f196])).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    spl2_5 <=> l1_pre_topc(sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    spl2_6 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.43  fof(f194,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | (~spl2_5 | ~spl2_6)),
% 0.22/0.43    inference(resolution,[],[f59,f55])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    l1_pre_topc(sK0) | ~spl2_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f53])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) ) | ~spl2_6),
% 0.22/0.43    inference(avatar_component_clause,[],[f58])).
% 0.22/0.43  fof(f167,plain,(
% 0.22/0.43    spl2_25 | ~spl2_22 | ~spl2_24),
% 0.22/0.43    inference(avatar_split_clause,[],[f159,f155,f143,f164])).
% 0.22/0.43  fof(f143,plain,(
% 0.22/0.43    spl2_22 <=> k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.43  fof(f159,plain,(
% 0.22/0.43    sK1 = k1_tops_1(sK0,sK1) | (~spl2_22 | ~spl2_24)),
% 0.22/0.43    inference(superposition,[],[f145,f157])).
% 0.22/0.43  fof(f145,plain,(
% 0.22/0.43    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~spl2_22),
% 0.22/0.43    inference(avatar_component_clause,[],[f143])).
% 0.22/0.43  fof(f158,plain,(
% 0.22/0.43    spl2_24 | ~spl2_3 | ~spl2_4 | ~spl2_23),
% 0.22/0.43    inference(avatar_split_clause,[],[f153,f149,f48,f43,f155])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    spl2_3 <=> v6_tops_1(sK1,sK0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.43  fof(f149,plain,(
% 0.22/0.43    spl2_23 <=> ! [X0] : (~v6_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.43  fof(f153,plain,(
% 0.22/0.43    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_23)),
% 0.22/0.43    inference(subsumption_resolution,[],[f152,f50])).
% 0.22/0.43  fof(f152,plain,(
% 0.22/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_23)),
% 0.22/0.43    inference(resolution,[],[f150,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    v6_tops_1(sK1,sK0) | ~spl2_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f43])).
% 0.22/0.43  fof(f150,plain,(
% 0.22/0.43    ( ! [X0] : (~v6_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0) ) | ~spl2_23),
% 0.22/0.43    inference(avatar_component_clause,[],[f149])).
% 0.22/0.43  fof(f151,plain,(
% 0.22/0.43    spl2_23 | ~spl2_5 | ~spl2_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f147,f66,f53,f149])).
% 0.22/0.43  fof(f66,plain,(
% 0.22/0.43    spl2_8 <=> ! [X1,X0] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.43  fof(f147,plain,(
% 0.22/0.43    ( ! [X0] : (~v6_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = X0) ) | (~spl2_5 | ~spl2_8)),
% 0.22/0.43    inference(resolution,[],[f67,f55])).
% 0.22/0.43  fof(f67,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) ) | ~spl2_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f66])).
% 0.22/0.43  fof(f146,plain,(
% 0.22/0.43    spl2_22 | ~spl2_12 | ~spl2_20),
% 0.22/0.43    inference(avatar_split_clause,[],[f140,f127,f83,f143])).
% 0.22/0.43  fof(f83,plain,(
% 0.22/0.43    spl2_12 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.43  fof(f140,plain,(
% 0.22/0.43    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | (~spl2_12 | ~spl2_20)),
% 0.22/0.43    inference(resolution,[],[f128,f84])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0))) ) | ~spl2_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f83])).
% 0.22/0.43  fof(f138,plain,(
% 0.22/0.43    ~spl2_4 | ~spl2_5 | ~spl2_9 | spl2_20),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f137])).
% 0.22/0.43  fof(f137,plain,(
% 0.22/0.43    $false | (~spl2_4 | ~spl2_5 | ~spl2_9 | spl2_20)),
% 0.22/0.43    inference(subsumption_resolution,[],[f136,f55])).
% 0.22/0.43  fof(f136,plain,(
% 0.22/0.43    ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_9 | spl2_20)),
% 0.22/0.43    inference(subsumption_resolution,[],[f135,f50])).
% 0.22/0.43  fof(f135,plain,(
% 0.22/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_9 | spl2_20)),
% 0.22/0.43    inference(resolution,[],[f129,f71])).
% 0.22/0.43  fof(f71,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f70])).
% 0.22/0.43  fof(f70,plain,(
% 0.22/0.43    spl2_9 <=> ! [X1,X0] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.43  fof(f129,plain,(
% 0.22/0.43    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_20),
% 0.22/0.43    inference(avatar_component_clause,[],[f127])).
% 0.22/0.43  fof(f109,plain,(
% 0.22/0.43    spl2_16 | ~spl2_4 | ~spl2_15),
% 0.22/0.43    inference(avatar_split_clause,[],[f103,f100,f48,f106])).
% 0.22/0.43  fof(f100,plain,(
% 0.22/0.43    spl2_15 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.43  fof(f103,plain,(
% 0.22/0.43    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) | (~spl2_4 | ~spl2_15)),
% 0.22/0.43    inference(resolution,[],[f101,f50])).
% 0.22/0.43  fof(f101,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | ~spl2_15),
% 0.22/0.43    inference(avatar_component_clause,[],[f100])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    spl2_15 | ~spl2_5 | ~spl2_11),
% 0.22/0.43    inference(avatar_split_clause,[],[f98,f78,f53,f100])).
% 0.22/0.43  fof(f78,plain,(
% 0.22/0.43    spl2_11 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k2_pre_topc(sK0,X0))) ) | (~spl2_5 | ~spl2_11)),
% 0.22/0.43    inference(resolution,[],[f79,f55])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))) ) | ~spl2_11),
% 0.22/0.43    inference(avatar_component_clause,[],[f78])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    spl2_12 | ~spl2_5 | ~spl2_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f81,f74,f53,f83])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    spl2_10 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k1_tops_1(sK0,k1_tops_1(sK0,X0))) ) | (~spl2_5 | ~spl2_10)),
% 0.22/0.43    inference(resolution,[],[f75,f55])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) ) | ~spl2_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f74])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    spl2_11),
% 0.22/0.43    inference(avatar_split_clause,[],[f31,f78])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(flattening,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.22/0.43  fof(f76,plain,(
% 0.22/0.43    spl2_10),
% 0.22/0.43    inference(avatar_split_clause,[],[f30,f74])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(flattening,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    spl2_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f29,f70])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(flattening,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    spl2_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f27,f66])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(nnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    spl2_6),
% 0.22/0.43    inference(avatar_split_clause,[],[f26,f58])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    spl2_5),
% 0.22/0.43    inference(avatar_split_clause,[],[f22,f53])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    l1_pre_topc(sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ((k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1)) & v6_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f19,f18])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : ((k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1))) & v6_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k2_tops_1(sK0,X1)) & v6_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ? [X1] : ((k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | k2_tops_1(sK0,k2_pre_topc(sK0,X1)) != k2_tops_1(sK0,X1)) & v6_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1)) & v6_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : ((k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1))) & v6_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.43    inference(flattening,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ? [X0] : (? [X1] : (((k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1))) & v6_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) => (k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) => (k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tops_1)).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    spl2_4),
% 0.22/0.43    inference(avatar_split_clause,[],[f23,f48])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl2_3),
% 0.22/0.43    inference(avatar_split_clause,[],[f24,f43])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    v6_tops_1(sK1,sK0)),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  fof(f41,plain,(
% 0.22/0.43    ~spl2_1 | ~spl2_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f32,f38,f34])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) != k2_tops_1(sK0,sK1) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1)),
% 0.22/0.43    inference(inner_rewriting,[],[f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k2_tops_1(sK0,sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f20])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (14447)------------------------------
% 0.22/0.43  % (14447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (14447)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (14447)Memory used [KB]: 10618
% 0.22/0.43  % (14447)Time elapsed: 0.010 s
% 0.22/0.43  % (14447)------------------------------
% 0.22/0.43  % (14447)------------------------------
% 0.22/0.43  % (14441)Success in time 0.068 s
%------------------------------------------------------------------------------
