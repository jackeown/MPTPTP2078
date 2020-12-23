%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:04 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 233 expanded)
%              Number of leaves         :   25 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  369 ( 912 expanded)
%              Number of equality atoms :   41 (  66 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (4630)Refutation not found, incomplete strategy% (4630)------------------------------
% (4630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4630)Termination reason: Refutation not found, incomplete strategy

% (4630)Memory used [KB]: 6140
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f60,f65,f70,f75,f81,f88,f94,f108,f115,f126,f127,f160,f161,f183,f200])).

% (4630)Time elapsed: 0.120 s
fof(f200,plain,
    ( ~ spl2_3
    | spl2_13
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f199,f181,f157,f85,f78,f119,f57])).

% (4630)------------------------------
% (4630)------------------------------
fof(f57,plain,
    ( spl2_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f119,plain,
    ( spl2_13
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f78,plain,
    ( spl2_7
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f85,plain,
    ( spl2_8
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f157,plain,
    ( spl2_17
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f181,plain,
    ( spl2_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f199,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_17
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f198,f159])).

fof(f159,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f157])).

fof(f198,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_18 ),
    inference(forward_demodulation,[],[f194,f87])).

fof(f87,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f194,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ spl2_7
    | ~ spl2_18 ),
    inference(resolution,[],[f182,f80])).

fof(f80,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f181])).

fof(f183,plain,
    ( ~ spl2_6
    | spl2_18
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f177,f72,f181,f72])).

fof(f72,plain,
    ( spl2_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))
        | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_6 ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))
        | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_6 ),
    inference(resolution,[],[f124,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f124,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) )
    | ~ spl2_6 ),
    inference(resolution,[],[f43,f74])).

fof(f74,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).

fof(f161,plain,
    ( ~ spl2_13
    | ~ spl2_6
    | ~ spl2_7
    | spl2_10 ),
    inference(avatar_split_clause,[],[f151,f98,f78,f72,f119])).

fof(f98,plain,
    ( spl2_10
  <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f151,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_6
    | ~ spl2_7
    | spl2_10 ),
    inference(unit_resulting_resolution,[],[f74,f99,f80,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f99,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f160,plain,
    ( spl2_17
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f152,f105,f78,f72,f157])).

fof(f105,plain,
    ( spl2_11
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f152,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_6
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f74,f107,f80,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
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

fof(f107,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f127,plain,
    ( spl2_2
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f116,f98,f72,f67,f51])).

fof(f51,plain,
    ( spl2_2
  <=> v6_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f67,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f116,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f74,f69,f100,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_tops_1)).

fof(f100,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f69,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f126,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f125,f91,f72,f67,f62,f112])).

fof(f112,plain,
    ( spl2_12
  <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f62,plain,
    ( spl2_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f91,plain,
    ( spl2_9
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f125,plain,
    ( sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f123,f93])).

fof(f93,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f91])).

fof(f123,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f74,f64,f69,f43])).

fof(f64,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f115,plain,
    ( ~ spl2_12
    | spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f109,f72,f67,f47,f112])).

fof(f47,plain,
    ( spl2_1
  <=> v5_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f109,plain,
    ( sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1))
    | spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f74,f49,f69,f39])).

fof(f49,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f108,plain,
    ( spl2_11
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f102,f72,f67,f62,f105])).

fof(f102,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f74,f64,f69,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f89,f72,f67,f57,f91])).

fof(f89,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f74,f59,f69,f42])).

fof(f59,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f88,plain,
    ( spl2_8
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f82,f67,f85])).

fof(f82,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f69,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f81,plain,
    ( spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f76,f67,f78])).

fof(f76,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f69,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f75,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ v6_tops_1(sK1,sK0)
      | ~ v5_tops_1(sK1,sK0) )
    & ( v6_tops_1(sK1,sK0)
      | v5_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v6_tops_1(X1,X0)
              | ~ v5_tops_1(X1,X0) )
            & ( v6_tops_1(X1,X0)
              | v5_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v6_tops_1(X1,sK0)
            | ~ v5_tops_1(X1,sK0) )
          & ( v6_tops_1(X1,sK0)
            | v5_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ( ~ v6_tops_1(X1,sK0)
          | ~ v5_tops_1(X1,sK0) )
        & ( v6_tops_1(X1,sK0)
          | v5_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v6_tops_1(sK1,sK0)
        | ~ v5_tops_1(sK1,sK0) )
      & ( v6_tops_1(sK1,sK0)
        | v5_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v4_pre_topc(X1,X0)
                & v3_pre_topc(X1,X0) )
             => ( v5_tops_1(X1,X0)
              <=> v6_tops_1(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0) )
           => ( v5_tops_1(X1,X0)
            <=> v6_tops_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tops_1)).

fof(f70,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f62])).

fof(f32,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f35,f51,f47])).

fof(f35,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:39:11 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.53  % (4639)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.23/0.53  % (4631)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.23/0.53  % (4631)Refutation not found, incomplete strategy% (4631)------------------------------
% 0.23/0.53  % (4631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (4631)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (4631)Memory used [KB]: 10618
% 0.23/0.53  % (4639)Refutation not found, incomplete strategy% (4639)------------------------------
% 0.23/0.53  % (4639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (4631)Time elapsed: 0.073 s
% 0.23/0.53  % (4631)------------------------------
% 0.23/0.53  % (4631)------------------------------
% 0.23/0.54  % (4639)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (4639)Memory used [KB]: 1663
% 0.23/0.54  % (4639)Time elapsed: 0.079 s
% 0.23/0.54  % (4639)------------------------------
% 0.23/0.54  % (4639)------------------------------
% 1.43/0.56  % (4625)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.43/0.56  % (4646)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.43/0.56  % (4628)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.43/0.56  % (4637)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.43/0.56  % (4633)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.43/0.57  % (4633)Refutation not found, incomplete strategy% (4633)------------------------------
% 1.43/0.57  % (4633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (4633)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (4633)Memory used [KB]: 10490
% 1.43/0.57  % (4633)Time elapsed: 0.131 s
% 1.43/0.57  % (4633)------------------------------
% 1.43/0.57  % (4633)------------------------------
% 1.43/0.57  % (4638)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.43/0.57  % (4629)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.43/0.57  % (4630)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.57  % (4627)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 1.61/0.57  % (4629)Refutation found. Thanks to Tanya!
% 1.61/0.57  % SZS status Theorem for theBenchmark
% 1.61/0.57  % SZS output start Proof for theBenchmark
% 1.61/0.57  % (4630)Refutation not found, incomplete strategy% (4630)------------------------------
% 1.61/0.57  % (4630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (4630)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (4630)Memory used [KB]: 6140
% 1.61/0.57  fof(f201,plain,(
% 1.61/0.57    $false),
% 1.61/0.57    inference(avatar_sat_refutation,[],[f54,f60,f65,f70,f75,f81,f88,f94,f108,f115,f126,f127,f160,f161,f183,f200])).
% 1.61/0.57  % (4630)Time elapsed: 0.120 s
% 1.61/0.57  fof(f200,plain,(
% 1.61/0.57    ~spl2_3 | spl2_13 | ~spl2_7 | ~spl2_8 | ~spl2_17 | ~spl2_18),
% 1.61/0.57    inference(avatar_split_clause,[],[f199,f181,f157,f85,f78,f119,f57])).
% 1.61/0.57  % (4630)------------------------------
% 1.61/0.57  % (4630)------------------------------
% 1.61/0.57  fof(f57,plain,(
% 1.61/0.57    spl2_3 <=> v4_pre_topc(sK1,sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.61/0.57  fof(f119,plain,(
% 1.61/0.57    spl2_13 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.61/0.57  fof(f78,plain,(
% 1.61/0.57    spl2_7 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.61/0.57  fof(f85,plain,(
% 1.61/0.57    spl2_8 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.61/0.57  fof(f157,plain,(
% 1.61/0.57    spl2_17 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.61/0.57  fof(f181,plain,(
% 1.61/0.57    spl2_18 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 1.61/0.57  fof(f199,plain,(
% 1.61/0.57    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~v4_pre_topc(sK1,sK0) | (~spl2_7 | ~spl2_8 | ~spl2_17 | ~spl2_18)),
% 1.61/0.57    inference(forward_demodulation,[],[f198,f159])).
% 1.61/0.57  fof(f159,plain,(
% 1.61/0.57    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_17),
% 1.61/0.57    inference(avatar_component_clause,[],[f157])).
% 1.61/0.57  fof(f198,plain,(
% 1.61/0.57    ~v4_pre_topc(sK1,sK0) | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_7 | ~spl2_8 | ~spl2_18)),
% 1.61/0.57    inference(forward_demodulation,[],[f194,f87])).
% 1.61/0.57  fof(f87,plain,(
% 1.61/0.57    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_8),
% 1.61/0.57    inference(avatar_component_clause,[],[f85])).
% 1.61/0.57  fof(f194,plain,(
% 1.61/0.57    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)),sK0) | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) | (~spl2_7 | ~spl2_18)),
% 1.61/0.57    inference(resolution,[],[f182,f80])).
% 1.61/0.57  fof(f80,plain,(
% 1.61/0.57    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 1.61/0.57    inference(avatar_component_clause,[],[f78])).
% 1.61/0.57  fof(f182,plain,(
% 1.61/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))) ) | ~spl2_18),
% 1.61/0.57    inference(avatar_component_clause,[],[f181])).
% 1.61/0.57  fof(f183,plain,(
% 1.61/0.57    ~spl2_6 | spl2_18 | ~spl2_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f177,f72,f181,f72])).
% 1.61/0.57  fof(f72,plain,(
% 1.61/0.57    spl2_6 <=> l1_pre_topc(sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.61/0.57  fof(f177,plain,(
% 1.61/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~l1_pre_topc(sK0)) ) | ~spl2_6),
% 1.61/0.57    inference(duplicate_literal_removal,[],[f176])).
% 1.61/0.57  fof(f176,plain,(
% 1.61/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_6),
% 1.61/0.57    inference(resolution,[],[f124,f41])).
% 1.61/0.57  fof(f41,plain,(
% 1.61/0.57    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f29])).
% 1.61/0.57  fof(f29,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(nnf_transformation,[],[f15])).
% 1.61/0.57  fof(f15,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f6])).
% 1.61/0.57  fof(f6,axiom,(
% 1.61/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 1.61/0.57  fof(f124,plain,(
% 1.61/0.57    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0)))) ) | ~spl2_6),
% 1.61/0.57    inference(resolution,[],[f43,f74])).
% 1.61/0.57  fof(f74,plain,(
% 1.61/0.57    l1_pre_topc(sK0) | ~spl2_6),
% 1.61/0.57    inference(avatar_component_clause,[],[f72])).
% 1.61/0.57  fof(f43,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f19])).
% 1.61/0.57  fof(f19,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(flattening,[],[f18])).
% 1.61/0.57  fof(f18,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f7])).
% 1.61/0.57  fof(f7,axiom,(
% 1.61/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tops_1)).
% 1.61/0.57  fof(f161,plain,(
% 1.61/0.57    ~spl2_13 | ~spl2_6 | ~spl2_7 | spl2_10),
% 1.61/0.57    inference(avatar_split_clause,[],[f151,f98,f78,f72,f119])).
% 1.61/0.57  fof(f98,plain,(
% 1.61/0.57    spl2_10 <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.61/0.57  fof(f151,plain,(
% 1.61/0.57    k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_6 | ~spl2_7 | spl2_10)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f74,f99,f80,f39])).
% 1.61/0.57  fof(f39,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v5_tops_1(X1,X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f28])).
% 1.61/0.57  fof(f28,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(nnf_transformation,[],[f14])).
% 1.61/0.57  fof(f14,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f4])).
% 1.61/0.57  fof(f4,axiom,(
% 1.61/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 1.61/0.57  fof(f99,plain,(
% 1.61/0.57    ~v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl2_10),
% 1.61/0.57    inference(avatar_component_clause,[],[f98])).
% 1.61/0.57  fof(f160,plain,(
% 1.61/0.57    spl2_17 | ~spl2_6 | ~spl2_7 | ~spl2_11),
% 1.61/0.57    inference(avatar_split_clause,[],[f152,f105,f78,f72,f157])).
% 1.61/0.57  fof(f105,plain,(
% 1.61/0.57    spl2_11 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.61/0.57  fof(f152,plain,(
% 1.61/0.57    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_6 | ~spl2_7 | ~spl2_11)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f74,f107,f80,f42])).
% 1.61/0.57  fof(f42,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f17])).
% 1.61/0.57  fof(f17,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(flattening,[],[f16])).
% 1.61/0.57  fof(f16,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f10])).
% 1.61/0.57  fof(f10,plain,(
% 1.61/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 1.61/0.57    inference(pure_predicate_removal,[],[f3])).
% 1.61/0.57  fof(f3,axiom,(
% 1.61/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.61/0.57  fof(f107,plain,(
% 1.61/0.57    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_11),
% 1.61/0.57    inference(avatar_component_clause,[],[f105])).
% 1.61/0.57  fof(f127,plain,(
% 1.61/0.57    spl2_2 | ~spl2_5 | ~spl2_6 | ~spl2_10),
% 1.61/0.57    inference(avatar_split_clause,[],[f116,f98,f72,f67,f51])).
% 1.61/0.57  fof(f51,plain,(
% 1.61/0.57    spl2_2 <=> v6_tops_1(sK1,sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.61/0.57  fof(f67,plain,(
% 1.61/0.57    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.61/0.57  fof(f116,plain,(
% 1.61/0.57    v6_tops_1(sK1,sK0) | (~spl2_5 | ~spl2_6 | ~spl2_10)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f74,f69,f100,f37])).
% 1.61/0.57  fof(f37,plain,(
% 1.61/0.57    ( ! [X0,X1] : (v6_tops_1(X1,X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f27])).
% 1.61/0.57  fof(f27,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(nnf_transformation,[],[f13])).
% 1.61/0.57  fof(f13,plain,(
% 1.61/0.57    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f5])).
% 1.61/0.57  fof(f5,axiom,(
% 1.61/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_tops_1)).
% 1.61/0.57  fof(f100,plain,(
% 1.61/0.57    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_10),
% 1.61/0.57    inference(avatar_component_clause,[],[f98])).
% 1.61/0.57  fof(f69,plain,(
% 1.61/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 1.61/0.57    inference(avatar_component_clause,[],[f67])).
% 1.61/0.57  fof(f126,plain,(
% 1.61/0.57    spl2_12 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_9),
% 1.61/0.57    inference(avatar_split_clause,[],[f125,f91,f72,f67,f62,f112])).
% 1.61/0.57  fof(f112,plain,(
% 1.61/0.57    spl2_12 <=> sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.61/0.57  fof(f62,plain,(
% 1.61/0.57    spl2_4 <=> v3_pre_topc(sK1,sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.61/0.57  fof(f91,plain,(
% 1.61/0.57    spl2_9 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.61/0.57  fof(f125,plain,(
% 1.61/0.57    sK1 = k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | (~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_9)),
% 1.61/0.57    inference(forward_demodulation,[],[f123,f93])).
% 1.61/0.57  fof(f93,plain,(
% 1.61/0.57    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_9),
% 1.61/0.57    inference(avatar_component_clause,[],[f91])).
% 1.61/0.57  fof(f123,plain,(
% 1.61/0.57    k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | (~spl2_4 | ~spl2_5 | ~spl2_6)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f74,f64,f69,f43])).
% 1.61/0.57  fof(f64,plain,(
% 1.61/0.57    v3_pre_topc(sK1,sK0) | ~spl2_4),
% 1.61/0.57    inference(avatar_component_clause,[],[f62])).
% 1.61/0.57  fof(f115,plain,(
% 1.61/0.57    ~spl2_12 | spl2_1 | ~spl2_5 | ~spl2_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f109,f72,f67,f47,f112])).
% 1.61/0.57  fof(f47,plain,(
% 1.61/0.57    spl2_1 <=> v5_tops_1(sK1,sK0)),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.61/0.57  fof(f109,plain,(
% 1.61/0.57    sK1 != k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) | (spl2_1 | ~spl2_5 | ~spl2_6)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f74,f49,f69,f39])).
% 1.61/0.57  fof(f49,plain,(
% 1.61/0.57    ~v5_tops_1(sK1,sK0) | spl2_1),
% 1.61/0.57    inference(avatar_component_clause,[],[f47])).
% 1.61/0.57  fof(f108,plain,(
% 1.61/0.57    spl2_11 | ~spl2_4 | ~spl2_5 | ~spl2_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f102,f72,f67,f62,f105])).
% 1.61/0.57  fof(f102,plain,(
% 1.61/0.57    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl2_4 | ~spl2_5 | ~spl2_6)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f74,f64,f69,f40])).
% 1.61/0.57  fof(f40,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f29])).
% 1.61/0.57  fof(f94,plain,(
% 1.61/0.57    spl2_9 | ~spl2_3 | ~spl2_5 | ~spl2_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f89,f72,f67,f57,f91])).
% 1.61/0.57  fof(f89,plain,(
% 1.61/0.57    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_3 | ~spl2_5 | ~spl2_6)),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f74,f59,f69,f42])).
% 1.61/0.57  fof(f59,plain,(
% 1.61/0.57    v4_pre_topc(sK1,sK0) | ~spl2_3),
% 1.61/0.57    inference(avatar_component_clause,[],[f57])).
% 1.61/0.57  fof(f88,plain,(
% 1.61/0.57    spl2_8 | ~spl2_5),
% 1.61/0.57    inference(avatar_split_clause,[],[f82,f67,f85])).
% 1.61/0.57  fof(f82,plain,(
% 1.61/0.57    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_5),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f69,f44])).
% 1.61/0.57  fof(f44,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f20])).
% 1.61/0.57  fof(f20,plain,(
% 1.61/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f2])).
% 1.61/0.57  fof(f2,axiom,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.61/0.57  fof(f81,plain,(
% 1.61/0.57    spl2_7 | ~spl2_5),
% 1.61/0.57    inference(avatar_split_clause,[],[f76,f67,f78])).
% 1.61/0.57  fof(f76,plain,(
% 1.61/0.57    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 1.61/0.57    inference(unit_resulting_resolution,[],[f69,f45])).
% 1.61/0.57  fof(f45,plain,(
% 1.61/0.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f21])).
% 1.61/0.57  fof(f21,plain,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f1])).
% 1.61/0.57  fof(f1,axiom,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.61/0.57  fof(f75,plain,(
% 1.61/0.57    spl2_6),
% 1.61/0.57    inference(avatar_split_clause,[],[f30,f72])).
% 1.61/0.57  fof(f30,plain,(
% 1.61/0.57    l1_pre_topc(sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f26,plain,(
% 1.61/0.57    ((~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)) & (v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.61/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 1.61/0.57  fof(f24,plain,(
% 1.61/0.57    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v6_tops_1(X1,sK0) | ~v5_tops_1(X1,sK0)) & (v6_tops_1(X1,sK0) | v5_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f25,plain,(
% 1.61/0.57    ? [X1] : ((~v6_tops_1(X1,sK0) | ~v5_tops_1(X1,sK0)) & (v6_tops_1(X1,sK0) | v5_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)) & (v6_tops_1(sK1,sK0) | v5_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.61/0.57    introduced(choice_axiom,[])).
% 1.61/0.57  fof(f23,plain,(
% 1.61/0.57    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.61/0.57    inference(flattening,[],[f22])).
% 1.61/0.57  fof(f22,plain,(
% 1.61/0.57    ? [X0] : (? [X1] : (((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.61/0.57    inference(nnf_transformation,[],[f12])).
% 1.61/0.57  fof(f12,plain,(
% 1.61/0.57    ? [X0] : (? [X1] : ((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.61/0.57    inference(flattening,[],[f11])).
% 1.61/0.57  fof(f11,plain,(
% 1.61/0.57    ? [X0] : (? [X1] : (((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.61/0.57    inference(ennf_transformation,[],[f9])).
% 1.61/0.57  fof(f9,negated_conjecture,(
% 1.61/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 1.61/0.57    inference(negated_conjecture,[],[f8])).
% 1.61/0.57  fof(f8,conjecture,(
% 1.61/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 1.61/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tops_1)).
% 1.61/0.57  fof(f70,plain,(
% 1.61/0.57    spl2_5),
% 1.61/0.57    inference(avatar_split_clause,[],[f31,f67])).
% 1.61/0.57  fof(f31,plain,(
% 1.61/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f65,plain,(
% 1.61/0.57    spl2_4),
% 1.61/0.57    inference(avatar_split_clause,[],[f32,f62])).
% 1.61/0.57  fof(f32,plain,(
% 1.61/0.57    v3_pre_topc(sK1,sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f60,plain,(
% 1.61/0.57    spl2_3),
% 1.61/0.57    inference(avatar_split_clause,[],[f33,f57])).
% 1.61/0.57  fof(f33,plain,(
% 1.61/0.57    v4_pre_topc(sK1,sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f54,plain,(
% 1.61/0.57    ~spl2_1 | ~spl2_2),
% 1.61/0.57    inference(avatar_split_clause,[],[f35,f51,f47])).
% 1.61/0.57  fof(f35,plain,(
% 1.61/0.57    ~v6_tops_1(sK1,sK0) | ~v5_tops_1(sK1,sK0)),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  % SZS output end Proof for theBenchmark
% 1.61/0.57  % (4629)------------------------------
% 1.61/0.57  % (4629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (4629)Termination reason: Refutation
% 1.61/0.57  
% 1.61/0.57  % (4629)Memory used [KB]: 10746
% 1.61/0.57  % (4629)Time elapsed: 0.125 s
% 1.61/0.57  % (4629)------------------------------
% 1.61/0.57  % (4629)------------------------------
% 1.61/0.57  % (4624)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.61/0.58  % (4622)Success in time 0.2 s
%------------------------------------------------------------------------------
