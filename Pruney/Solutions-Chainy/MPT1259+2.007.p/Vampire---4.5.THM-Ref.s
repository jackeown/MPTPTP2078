%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 273 expanded)
%              Number of leaves         :   42 ( 124 expanded)
%              Depth                    :    8
%              Number of atoms          :  501 ( 825 expanded)
%              Number of equality atoms :  100 ( 171 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f433,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f66,f70,f75,f86,f90,f101,f118,f123,f133,f137,f141,f151,f156,f167,f174,f178,f203,f212,f229,f260,f270,f330,f404,f413,f418,f429])).

fof(f429,plain,
    ( spl2_13
    | ~ spl2_28
    | ~ spl2_29
    | ~ spl2_35
    | ~ spl2_54
    | ~ spl2_55 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | spl2_13
    | ~ spl2_28
    | ~ spl2_29
    | ~ spl2_35
    | ~ spl2_54
    | ~ spl2_55 ),
    inference(subsumption_resolution,[],[f427,f117])).

fof(f117,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_13
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f427,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_28
    | ~ spl2_29
    | ~ spl2_35
    | ~ spl2_54
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f426,f412])).

fof(f412,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl2_54
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f426,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_28
    | ~ spl2_29
    | ~ spl2_35
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f425,f211])).

fof(f211,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl2_28
  <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f425,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0)
    | ~ spl2_29
    | ~ spl2_35
    | ~ spl2_55 ),
    inference(forward_demodulation,[],[f421,f269])).

fof(f269,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl2_35
  <=> k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f421,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ spl2_29
    | ~ spl2_55 ),
    inference(resolution,[],[f417,f219])).

fof(f219,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl2_29
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f417,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_55 ),
    inference(avatar_component_clause,[],[f416])).

fof(f416,plain,
    ( spl2_55
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).

fof(f418,plain,
    ( spl2_55
    | ~ spl2_2
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f414,f328,f54,f416])).

fof(f54,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f328,plain,
    ( spl2_44
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f414,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) )
    | ~ spl2_2
    | ~ spl2_44 ),
    inference(resolution,[],[f329,f56])).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f329,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f328])).

fof(f413,plain,
    ( spl2_54
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f408,f402,f121,f99,f410])).

fof(f99,plain,
    ( spl2_10
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f121,plain,
    ( spl2_14
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f402,plain,
    ( spl2_53
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f408,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_10
    | ~ spl2_14
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f407,f100])).

fof(f100,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f407,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_14
    | ~ spl2_53 ),
    inference(superposition,[],[f403,f122])).

fof(f122,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f403,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f402])).

fof(f404,plain,
    ( spl2_53
    | ~ spl2_17
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f233,f218,f139,f402])).

fof(f139,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f233,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))
    | ~ spl2_17
    | ~ spl2_29 ),
    inference(resolution,[],[f219,f140])).

fof(f140,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f330,plain,(
    spl2_44 ),
    inference(avatar_split_clause,[],[f35,f328])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f270,plain,
    ( spl2_35
    | ~ spl2_3
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f261,f258,f59,f267])).

fof(f59,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f258,plain,
    ( spl2_34
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f261,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_3
    | ~ spl2_34 ),
    inference(resolution,[],[f259,f61])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f258])).

fof(f260,plain,
    ( spl2_34
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f256,f172,f54,f49,f258])).

fof(f49,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f172,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f255,f56])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) )
    | ~ spl2_1
    | ~ spl2_23 ),
    inference(resolution,[],[f173,f51])).

fof(f51,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f172])).

fof(f229,plain,
    ( ~ spl2_2
    | ~ spl2_16
    | ~ spl2_26
    | spl2_29 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_26
    | spl2_29 ),
    inference(subsumption_resolution,[],[f227,f56])).

fof(f227,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_16
    | ~ spl2_26
    | spl2_29 ),
    inference(subsumption_resolution,[],[f226,f193])).

fof(f193,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl2_26
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f226,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_16
    | spl2_29 ),
    inference(resolution,[],[f220,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f220,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_29 ),
    inference(avatar_component_clause,[],[f218])).

fof(f212,plain,
    ( spl2_28
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f206,f192,f176,f209])).

fof(f176,plain,
    ( spl2_24
  <=> ! [X0] :
        ( k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f206,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ spl2_24
    | ~ spl2_26 ),
    inference(resolution,[],[f193,f177])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f176])).

fof(f203,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16
    | spl2_26 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_16
    | spl2_26 ),
    inference(subsumption_resolution,[],[f201,f56])).

fof(f201,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_16
    | spl2_26 ),
    inference(subsumption_resolution,[],[f200,f61])).

fof(f200,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_16
    | spl2_26 ),
    inference(resolution,[],[f194,f136])).

fof(f194,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_26 ),
    inference(avatar_component_clause,[],[f192])).

fof(f178,plain,
    ( spl2_24
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f170,f165,f135,f54,f176])).

fof(f165,plain,
    ( spl2_22
  <=> ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f170,plain,
    ( ! [X0] :
        ( k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f169,f56])).

fof(f169,plain,
    ( ! [X0] :
        ( k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,
    ( ! [X0] :
        ( k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_16
    | ~ spl2_22 ),
    inference(resolution,[],[f166,f136])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f165])).

fof(f174,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f39,f172])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).

fof(f167,plain,
    ( spl2_22
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f159,f154,f131,f54,f49,f165])).

fof(f131,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( v4_pre_topc(k2_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f154,plain,
    ( spl2_20
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f158,f51])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_2
    | ~ spl2_15
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f157,f56])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl2_15
    | ~ spl2_20 ),
    inference(resolution,[],[f155,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k2_tops_1(X0,X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f154])).

fof(f156,plain,
    ( spl2_20
    | ~ spl2_2
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f152,f149,f54,f154])).

fof(f149,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl2_2
    | ~ spl2_19 ),
    inference(resolution,[],[f150,f56])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f36,f149])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f141,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f47,f139])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f137,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f44,f135])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f133,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f43,f131])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_tops_1)).

fof(f123,plain,
    ( spl2_14
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f91,f84,f73,f121])).

fof(f73,plain,
    ( spl2_6
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f84,plain,
    ( spl2_8
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f91,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f85,f74])).

fof(f74,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f85,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f118,plain,(
    ~ spl2_13 ),
    inference(avatar_split_clause,[],[f33,f115])).

fof(f33,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).

fof(f101,plain,
    ( spl2_10
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f97,f88,f84,f73,f99])).

fof(f88,plain,
    ( spl2_9
  <=> ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f97,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f89,f91])).

fof(f89,plain,
    ( ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f86,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f75,plain,
    ( spl2_6
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f71,f68,f64,f73])).

fof(f64,plain,
    ( spl2_4
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f68,plain,
    ( spl2_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f71,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(resolution,[],[f69,f65])).

fof(f65,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f70,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f66,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f40,f64])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f62,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f31,f54])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f30,f49])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (13793)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (13787)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (13793)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f433,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f52,f57,f62,f66,f70,f75,f86,f90,f101,f118,f123,f133,f137,f141,f151,f156,f167,f174,f178,f203,f212,f229,f260,f270,f330,f404,f413,f418,f429])).
% 0.21/0.48  fof(f429,plain,(
% 0.21/0.48    spl2_13 | ~spl2_28 | ~spl2_29 | ~spl2_35 | ~spl2_54 | ~spl2_55),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f428])).
% 0.21/0.48  fof(f428,plain,(
% 0.21/0.48    $false | (spl2_13 | ~spl2_28 | ~spl2_29 | ~spl2_35 | ~spl2_54 | ~spl2_55)),
% 0.21/0.48    inference(subsumption_resolution,[],[f427,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | spl2_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl2_13 <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.48  fof(f427,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_28 | ~spl2_29 | ~spl2_35 | ~spl2_54 | ~spl2_55)),
% 0.21/0.48    inference(forward_demodulation,[],[f426,f412])).
% 0.21/0.48  fof(f412,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | ~spl2_54),
% 0.21/0.48    inference(avatar_component_clause,[],[f410])).
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    spl2_54 <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 0.21/0.48  fof(f426,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | (~spl2_28 | ~spl2_29 | ~spl2_35 | ~spl2_55)),
% 0.21/0.48    inference(forward_demodulation,[],[f425,f211])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~spl2_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f209])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    spl2_28 <=> k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.48  fof(f425,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) | (~spl2_29 | ~spl2_35 | ~spl2_55)),
% 0.21/0.48    inference(forward_demodulation,[],[f421,f269])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~spl2_35),
% 0.21/0.48    inference(avatar_component_clause,[],[f267])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    spl2_35 <=> k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.21/0.48  fof(f421,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | (~spl2_29 | ~spl2_55)),
% 0.21/0.48    inference(resolution,[],[f417,f219])).
% 0.21/0.48  fof(f219,plain,(
% 0.21/0.48    m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f218])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    spl2_29 <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.48  fof(f417,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | ~spl2_55),
% 0.21/0.48    inference(avatar_component_clause,[],[f416])).
% 0.21/0.48  fof(f416,plain,(
% 0.21/0.48    spl2_55 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_55])])).
% 0.21/0.48  fof(f418,plain,(
% 0.21/0.48    spl2_55 | ~spl2_2 | ~spl2_44),
% 0.21/0.48    inference(avatar_split_clause,[],[f414,f328,f54,f416])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    spl2_44 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.21/0.48  fof(f414,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) ) | (~spl2_2 | ~spl2_44)),
% 0.21/0.48    inference(resolution,[],[f329,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f54])).
% 0.21/0.48  fof(f329,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) ) | ~spl2_44),
% 0.21/0.48    inference(avatar_component_clause,[],[f328])).
% 0.21/0.48  fof(f413,plain,(
% 0.21/0.48    spl2_54 | ~spl2_10 | ~spl2_14 | ~spl2_53),
% 0.21/0.48    inference(avatar_split_clause,[],[f408,f402,f121,f99,f410])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl2_10 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl2_14 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.48  fof(f402,plain,(
% 0.21/0.48    spl2_53 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.21/0.48  fof(f408,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | (~spl2_10 | ~spl2_14 | ~spl2_53)),
% 0.21/0.48    inference(forward_demodulation,[],[f407,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f407,plain,(
% 0.21/0.48    k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | (~spl2_14 | ~spl2_53)),
% 0.21/0.48    inference(superposition,[],[f403,f122])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl2_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f121])).
% 0.21/0.48  fof(f403,plain,(
% 0.21/0.48    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))) ) | ~spl2_53),
% 0.21/0.48    inference(avatar_component_clause,[],[f402])).
% 0.21/0.48  fof(f404,plain,(
% 0.21/0.48    spl2_53 | ~spl2_17 | ~spl2_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f233,f218,f139,f402])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl2_17 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k5_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k3_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0))) ) | (~spl2_17 | ~spl2_29)),
% 0.21/0.48    inference(resolution,[],[f219,f140])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) | ~spl2_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f139])).
% 0.21/0.48  fof(f330,plain,(
% 0.21/0.48    spl2_44),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f328])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    spl2_35 | ~spl2_3 | ~spl2_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f261,f258,f59,f267])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    spl2_34 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.48  fof(f261,plain,(
% 0.21/0.48    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_3 | ~spl2_34)),
% 0.21/0.48    inference(resolution,[],[f259,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) ) | ~spl2_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f258])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    spl2_34 | ~spl2_1 | ~spl2_2 | ~spl2_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f256,f172,f54,f49,f258])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl2_23 <=> ! [X1,X0] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_23)),
% 0.21/0.48    inference(subsumption_resolution,[],[f255,f56])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0)))) ) | (~spl2_1 | ~spl2_23)),
% 0.21/0.48    inference(resolution,[],[f173,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))) ) | ~spl2_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f172])).
% 0.21/0.48  fof(f229,plain,(
% 0.21/0.48    ~spl2_2 | ~spl2_16 | ~spl2_26 | spl2_29),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f228])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    $false | (~spl2_2 | ~spl2_16 | ~spl2_26 | spl2_29)),
% 0.21/0.48    inference(subsumption_resolution,[],[f227,f56])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (~spl2_16 | ~spl2_26 | spl2_29)),
% 0.21/0.48    inference(subsumption_resolution,[],[f226,f193])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f192])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    spl2_26 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_16 | spl2_29)),
% 0.21/0.48    inference(resolution,[],[f220,f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    spl2_16 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ~m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f218])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    spl2_28 | ~spl2_24 | ~spl2_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f206,f192,f176,f209])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl2_24 <=> ! [X0] : (k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | (~spl2_24 | ~spl2_26)),
% 0.21/0.48    inference(resolution,[],[f193,f177])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0))) ) | ~spl2_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f176])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ~spl2_2 | ~spl2_3 | ~spl2_16 | spl2_26),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f202])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    $false | (~spl2_2 | ~spl2_3 | ~spl2_16 | spl2_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f201,f56])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_16 | spl2_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f200,f61])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_16 | spl2_26)),
% 0.21/0.48    inference(resolution,[],[f194,f136])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f192])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl2_24 | ~spl2_2 | ~spl2_16 | ~spl2_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f170,f165,f135,f54,f176])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    spl2_22 <=> ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_2 | ~spl2_16 | ~spl2_22)),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f56])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_16 | ~spl2_22)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f168])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ( ! [X0] : (k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | (~spl2_16 | ~spl2_22)),
% 0.21/0.48    inference(resolution,[],[f166,f136])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f165])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    spl2_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f172])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l80_tops_1)).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    spl2_22 | ~spl2_1 | ~spl2_2 | ~spl2_15 | ~spl2_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f159,f154,f131,f54,f49,f165])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl2_15 <=> ! [X1,X0] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl2_20 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_15 | ~spl2_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f158,f51])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) ) | (~spl2_2 | ~spl2_15 | ~spl2_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f157,f56])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k2_pre_topc(sK0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl2_15 | ~spl2_20)),
% 0.21/0.48    inference(resolution,[],[f155,f132])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl2_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl2_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f154])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl2_20 | ~spl2_2 | ~spl2_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f152,f149,f54,f154])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    spl2_19 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | (~spl2_2 | ~spl2_19)),
% 0.21/0.48    inference(resolution,[],[f150,f56])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) ) | ~spl2_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f149])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    spl2_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f149])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl2_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f139])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f45,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    spl2_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f135])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    spl2_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f131])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_tops_1(X0,X1),X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_tops_1)).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    spl2_14 | ~spl2_6 | ~spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f91,f84,f73,f121])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl2_6 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl2_8 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl2_6 | ~spl2_8)),
% 0.21/0.48    inference(superposition,[],[f85,f74])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl2_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ~spl2_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f115])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f28,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_tops_1)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl2_10 | ~spl2_6 | ~spl2_8 | ~spl2_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f97,f88,f84,f73,f99])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl2_9 <=> ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_6 | ~spl2_8 | ~spl2_9)),
% 0.21/0.48    inference(backward_demodulation,[],[f89,f91])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) ) | ~spl2_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl2_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f46,f88])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f34,f42])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl2_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f84])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl2_6 | ~spl2_4 | ~spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f71,f68,f64,f73])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl2_4 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl2_5 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.48    inference(resolution,[],[f69,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f64])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl2_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f68])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl2_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f68])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl2_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f64])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl2_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f59])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl2_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f54])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl2_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f49])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (13793)------------------------------
% 0.21/0.48  % (13793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13793)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (13793)Memory used [KB]: 6396
% 0.21/0.48  % (13793)Time elapsed: 0.019 s
% 0.21/0.48  % (13793)------------------------------
% 0.21/0.48  % (13793)------------------------------
% 0.21/0.48  % (13780)Success in time 0.121 s
%------------------------------------------------------------------------------
