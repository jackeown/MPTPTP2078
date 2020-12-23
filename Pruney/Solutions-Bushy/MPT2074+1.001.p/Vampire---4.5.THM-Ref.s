%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2074+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 630 expanded)
%              Number of leaves         :   49 ( 267 expanded)
%              Depth                    :   11
%              Number of atoms          : 1298 (3374 expanded)
%              Number of equality atoms :    5 (  60 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f110,f114,f118,f122,f126,f131,f135,f148,f153,f163,f217,f219,f247,f249,f253,f308,f344,f352,f354,f356,f358,f362,f364,f366,f368,f371,f373,f378,f434,f438,f441,f444,f448,f454])).

fof(f454,plain,
    ( spl7_24
    | ~ spl7_10
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6
    | spl7_12
    | ~ spl7_2
    | ~ spl7_11
    | ~ spl7_57 ),
    inference(avatar_split_clause,[],[f453,f429,f146,f104,f151,f120,f112,f108,f143,f212])).

fof(f212,plain,
    ( spl7_24
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f143,plain,
    ( spl7_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f108,plain,
    ( spl7_3
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f112,plain,
    ( spl7_4
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f120,plain,
    ( spl7_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f151,plain,
    ( spl7_12
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f104,plain,
    ( spl7_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f146,plain,
    ( spl7_11
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f429,plain,
    ( spl7_57
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f453,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_57 ),
    inference(forward_demodulation,[],[f450,f137])).

fof(f137,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f136,f67])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r1_waybel_7(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ( v1_compts_1(X0)
      <~> ! [X1] :
            ( ? [X2] :
                ( r1_waybel_7(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            | v1_xboole_0(X1) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v1_compts_1(X0)
        <=> ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
                & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
                & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
                & ~ v1_xboole_0(X1) )
             => ? [X2] :
                  ( r1_waybel_7(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( r1_waybel_7(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow19)).

fof(f136,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f69,f71])).

fof(f71,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f450,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_57 ),
    inference(resolution,[],[f430,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f430,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f429])).

fof(f448,plain,
    ( spl7_57
    | ~ spl7_56
    | ~ spl7_55
    | ~ spl7_54
    | ~ spl7_48
    | spl7_58 ),
    inference(avatar_split_clause,[],[f446,f432,f376,f420,f423,f426,f429])).

fof(f426,plain,
    ( spl7_56
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f423,plain,
    ( spl7_55
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f420,plain,
    ( spl7_54
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f376,plain,
    ( spl7_48
  <=> ! [X0] :
        ( m1_subset_1(sK3(sK0,X0),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f432,plain,
    ( spl7_58
  <=> m1_subset_1(sK3(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f446,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_48
    | spl7_58 ),
    inference(resolution,[],[f377,f433])).

fof(f433,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | spl7_58 ),
    inference(avatar_component_clause,[],[f432])).

fof(f377,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0,X0),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f376])).

fof(f444,plain,
    ( spl7_24
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6
    | spl7_12
    | ~ spl7_10
    | ~ spl7_11
    | spl7_54 ),
    inference(avatar_split_clause,[],[f443,f420,f146,f143,f151,f120,f112,f108,f104,f212])).

fof(f443,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl7_54 ),
    inference(forward_demodulation,[],[f442,f137])).

fof(f442,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl7_54 ),
    inference(resolution,[],[f421,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f421,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | spl7_54 ),
    inference(avatar_component_clause,[],[f420])).

fof(f441,plain,
    ( spl7_24
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6
    | spl7_12
    | ~ spl7_10
    | ~ spl7_11
    | spl7_56 ),
    inference(avatar_split_clause,[],[f440,f426,f146,f143,f151,f120,f112,f108,f104,f212])).

fof(f440,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl7_56 ),
    inference(forward_demodulation,[],[f439,f137])).

fof(f439,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl7_56 ),
    inference(resolution,[],[f427,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f427,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl7_56 ),
    inference(avatar_component_clause,[],[f426])).

fof(f438,plain,
    ( spl7_24
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | spl7_12
    | ~ spl7_10
    | ~ spl7_11
    | spl7_55 ),
    inference(avatar_split_clause,[],[f436,f423,f146,f143,f151,f120,f116,f112,f108,f104,f212])).

fof(f116,plain,
    ( spl7_5
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f436,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl7_55 ),
    inference(forward_demodulation,[],[f435,f137])).

fof(f435,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl7_55 ),
    inference(resolution,[],[f424,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f424,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl7_55 ),
    inference(avatar_component_clause,[],[f423])).

fof(f434,plain,
    ( ~ spl7_54
    | ~ spl7_55
    | ~ spl7_56
    | spl7_57
    | ~ spl7_1
    | spl7_24
    | ~ spl7_30
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_29
    | ~ spl7_58
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f418,f124,f432,f239,f120,f116,f112,f108,f104,f242,f212,f101,f429,f426,f423,f420])).

fof(f101,plain,
    ( spl7_1
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f242,plain,
    ( spl7_30
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f239,plain,
    ( spl7_29
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f124,plain,
    ( spl7_7
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f418,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_7 ),
    inference(duplicate_literal_removal,[],[f417])).

fof(f417,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f413,f137])).

fof(f413,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ m1_subset_1(sK3(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_7 ),
    inference(resolution,[],[f379,f297])).

fof(f297,plain,(
    ! [X4,X3] :
      ( r1_waybel_7(X3,X4,sK3(X3,k3_yellow19(X3,k2_struct_0(X3),X4)))
      | ~ l1_pre_topc(X3)
      | v1_xboole_0(X4)
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3))))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3)))))
      | ~ m1_subset_1(sK3(X3,k3_yellow19(X3,k2_struct_0(X3),X4)),u1_struct_0(X3))
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X3)
      | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3) ) ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,(
    ! [X4,X3] :
      ( ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v1_xboole_0(X4)
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3))))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3)))))
      | ~ m1_subset_1(sK3(X3,k3_yellow19(X3,k2_struct_0(X3),X4)),u1_struct_0(X3))
      | r1_waybel_7(X3,X4,sK3(X3,k3_yellow19(X3,k2_struct_0(X3),X4)))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_compts_1(X3)
      | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f81,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK3(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( r3_waybel_9(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_compts_1(X0)
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( r3_waybel_9(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l37_yellow19)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_7(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).

fof(f379,plain,
    ( ! [X2] :
        ( ~ r1_waybel_7(sK0,sK1,X2)
        | ~ m1_subset_1(X2,k2_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f125,f137])).

fof(f125,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X2) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f378,plain,
    ( ~ spl7_1
    | spl7_48 ),
    inference(avatar_split_clause,[],[f374,f376,f101])).

fof(f374,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,X0),k2_struct_0(sK0))
      | ~ v1_compts_1(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0) ) ),
    inference(global_subsumption,[],[f65,f66,f67,f221])).

fof(f221,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,X0),k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_compts_1(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f72,f137])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f373,plain,
    ( spl7_24
    | ~ spl7_40
    | spl7_37
    | ~ spl7_10
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f372,f327,f143,f315,f324,f212])).

fof(f324,plain,
    ( spl7_40
  <=> l1_waybel_0(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f315,plain,
    ( spl7_37
  <=> v2_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f327,plain,
    ( spl7_41
  <=> v1_xboole_0(k2_yellow19(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f372,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_41 ),
    inference(resolution,[],[f328,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_yellow19(X0,X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_yellow19)).

fof(f328,plain,
    ( v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f327])).

fof(f371,plain,
    ( ~ spl7_44
    | ~ spl7_43
    | spl7_37
    | spl7_41
    | ~ spl7_40
    | ~ spl7_38
    | ~ spl7_39
    | ~ spl7_36
    | spl7_46 ),
    inference(avatar_split_clause,[],[f369,f342,f306,f321,f318,f324,f327,f315,f333,f336])).

fof(f336,plain,
    ( spl7_44
  <=> v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f333,plain,
    ( spl7_43
  <=> v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f318,plain,
    ( spl7_38
  <=> v4_orders_2(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f321,plain,
    ( spl7_39
  <=> v7_waybel_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f306,plain,
    ( spl7_36
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f342,plain,
    ( spl7_46
  <=> m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f369,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | v2_struct_0(sK4(sK0))
    | ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl7_36
    | spl7_46 ),
    inference(resolution,[],[f307,f343])).

fof(f343,plain,
    ( ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),k2_struct_0(sK0))
    | spl7_46 ),
    inference(avatar_component_clause,[],[f342])).

fof(f307,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0))) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f306])).

fof(f368,plain,
    ( spl7_24
    | ~ spl7_40
    | spl7_37
    | ~ spl7_10
    | spl7_42 ),
    inference(avatar_split_clause,[],[f367,f330,f143,f315,f324,f212])).

fof(f330,plain,
    ( spl7_42
  <=> m1_subset_1(k2_yellow19(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f367,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | spl7_42 ),
    inference(resolution,[],[f331,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow19)).

fof(f331,plain,
    ( ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | spl7_42 ),
    inference(avatar_component_clause,[],[f330])).

fof(f366,plain,
    ( spl7_24
    | ~ spl7_40
    | ~ spl7_39
    | ~ spl7_38
    | spl7_37
    | ~ spl7_10
    | spl7_45 ),
    inference(avatar_split_clause,[],[f365,f339,f143,f315,f318,f321,f324,f212])).

fof(f339,plain,
    ( spl7_45
  <=> v1_subset_1(k2_yellow19(sK0,sK4(sK0)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f365,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | spl7_45 ),
    inference(resolution,[],[f340,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_yellow19)).

fof(f340,plain,
    ( ~ v1_subset_1(k2_yellow19(sK0,sK4(sK0)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | spl7_45 ),
    inference(avatar_component_clause,[],[f339])).

fof(f364,plain,
    ( spl7_24
    | ~ spl7_40
    | ~ spl7_39
    | ~ spl7_38
    | spl7_37
    | ~ spl7_10
    | spl7_44 ),
    inference(avatar_split_clause,[],[f363,f336,f143,f315,f318,f321,f324,f212])).

fof(f363,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | spl7_44 ),
    inference(resolution,[],[f337,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f337,plain,
    ( ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | spl7_44 ),
    inference(avatar_component_clause,[],[f336])).

fof(f362,plain,
    ( spl7_1
    | spl7_24
    | ~ spl7_29
    | ~ spl7_30
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f361,f315,f242,f239,f212,f101])).

fof(f361,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_37 ),
    inference(resolution,[],[f316,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ? [X1] :
          ( ! [X2] :
              ( ~ r3_waybel_9(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & r2_hidden(X1,k6_yellow_6(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r3_waybel_9(X0,X1,X2) )
                & r2_hidden(X1,k6_yellow_6(X0)) ) )
       => v1_compts_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_yellow19)).

fof(f316,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f315])).

fof(f358,plain,
    ( spl7_24
    | ~ spl7_40
    | spl7_37
    | ~ spl7_10
    | spl7_43 ),
    inference(avatar_split_clause,[],[f357,f333,f143,f315,f324,f212])).

fof(f357,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | spl7_43 ),
    inference(resolution,[],[f334,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f334,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | spl7_43 ),
    inference(avatar_component_clause,[],[f333])).

fof(f356,plain,
    ( spl7_1
    | spl7_24
    | ~ spl7_29
    | ~ spl7_30
    | spl7_40 ),
    inference(avatar_split_clause,[],[f355,f324,f242,f239,f212,f101])).

fof(f355,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | spl7_40 ),
    inference(resolution,[],[f325,f78])).

fof(f78,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f325,plain,
    ( ~ l1_waybel_0(sK4(sK0),sK0)
    | spl7_40 ),
    inference(avatar_component_clause,[],[f324])).

fof(f354,plain,
    ( spl7_1
    | spl7_24
    | ~ spl7_29
    | ~ spl7_30
    | spl7_39 ),
    inference(avatar_split_clause,[],[f353,f321,f242,f239,f212,f101])).

fof(f353,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | spl7_39 ),
    inference(resolution,[],[f322,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v7_waybel_0(sK4(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f322,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | spl7_39 ),
    inference(avatar_component_clause,[],[f321])).

fof(f352,plain,
    ( spl7_1
    | spl7_24
    | ~ spl7_29
    | ~ spl7_30
    | spl7_38 ),
    inference(avatar_split_clause,[],[f351,f318,f242,f239,f212,f101])).

fof(f351,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | spl7_38 ),
    inference(resolution,[],[f319,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v4_orders_2(sK4(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f319,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | spl7_38 ),
    inference(avatar_component_clause,[],[f318])).

fof(f344,plain,
    ( spl7_1
    | spl7_24
    | ~ spl7_29
    | ~ spl7_30
    | spl7_37
    | ~ spl7_38
    | ~ spl7_39
    | ~ spl7_40
    | spl7_41
    | ~ spl7_42
    | ~ spl7_43
    | ~ spl7_44
    | ~ spl7_45
    | ~ spl7_46
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f313,f245,f342,f339,f336,f333,f330,f327,f324,f321,f318,f315,f242,f239,f212,f101])).

fof(f245,plain,
    ( spl7_31
  <=> ! [X0] :
        ( ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_yellow19(sK0,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0)))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f313,plain,
    ( ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),k2_struct_0(sK0))
    | ~ v1_subset_1(k2_yellow19(sK0,sK4(sK0)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_31 ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,
    ( ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),k2_struct_0(sK0))
    | ~ v1_subset_1(k2_yellow19(sK0,sK4(sK0)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),k2_struct_0(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_31 ),
    inference(forward_demodulation,[],[f310,f137])).

fof(f310,plain,
    ( ~ v1_subset_1(k2_yellow19(sK0,sK4(sK0)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k2_yellow19(sK0,sK4(sK0)),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),k2_struct_0(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | v2_struct_0(sK4(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_31 ),
    inference(resolution,[],[f246,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK4(X0),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f246,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0)))
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(k2_yellow19(sK0,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f245])).

fof(f308,plain,
    ( spl7_24
    | ~ spl7_10
    | spl7_36
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f304,f215,f306,f143,f212])).

fof(f215,plain,
    ( spl7_25
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f304,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ l1_struct_0(sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl7_25 ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_25 ),
    inference(resolution,[],[f216,f87])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f215])).

fof(f253,plain,(
    spl7_30 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | spl7_30 ),
    inference(resolution,[],[f243,f66])).

fof(f243,plain,
    ( ~ v2_pre_topc(sK0)
    | spl7_30 ),
    inference(avatar_component_clause,[],[f242])).

fof(f249,plain,(
    spl7_29 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl7_29 ),
    inference(resolution,[],[f240,f67])).

fof(f240,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_29 ),
    inference(avatar_component_clause,[],[f239])).

fof(f247,plain,
    ( spl7_24
    | ~ spl7_29
    | ~ spl7_30
    | spl7_31
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f237,f129,f245,f242,f239,f212])).

fof(f129,plain,
    ( spl7_8
  <=> ! [X1] :
        ( v1_xboole_0(X1)
        | r1_waybel_7(sK0,X1,sK2(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | ~ m1_subset_1(k2_yellow19(sK0,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f236,f137])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | ~ m1_subset_1(k2_yellow19(sK0,X0),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_8 ),
    inference(resolution,[],[f82,f130])).

fof(f130,plain,
    ( ! [X1] :
        ( r1_waybel_7(sK0,X1,sK2(X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

% (17945)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).

fof(f219,plain,(
    ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl7_24 ),
    inference(resolution,[],[f213,f65])).

fof(f213,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f212])).

fof(f217,plain,
    ( spl7_24
    | spl7_25
    | ~ spl7_10
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f209,f133,f143,f215,f212])).

fof(f133,plain,
    ( spl7_9
  <=> ! [X1] :
        ( v1_xboole_0(X1)
        | m1_subset_1(sK2(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0)
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_9 ),
    inference(resolution,[],[f89,f190])).

fof(f190,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | v1_xboole_0(X1)
        | m1_subset_1(sK2(X1),k2_struct_0(sK0))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f134,f137])).

fof(f134,plain,
    ( ! [X1] :
        ( v1_xboole_0(X1)
        | m1_subset_1(sK2(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f163,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl7_10 ),
    inference(resolution,[],[f161,f67])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_10 ),
    inference(resolution,[],[f144,f71])).

fof(f144,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f153,plain,
    ( ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f149,f151,f143])).

fof(f149,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(global_subsumption,[],[f65,f140])).

fof(f140,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f84,f137])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f148,plain,
    ( ~ spl7_10
    | spl7_11 ),
    inference(avatar_split_clause,[],[f139,f146,f143])).

fof(f139,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f70,f137])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f135,plain,
    ( spl7_1
    | spl7_9 ),
    inference(avatar_split_clause,[],[f57,f133,f101])).

fof(f57,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | m1_subset_1(sK2(X1),u1_struct_0(sK0))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f131,plain,
    ( spl7_1
    | spl7_8 ),
    inference(avatar_split_clause,[],[f58,f129,f101])).

fof(f58,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | r1_waybel_7(sK0,X1,sK2(X1))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f126,plain,
    ( ~ spl7_1
    | spl7_7 ),
    inference(avatar_split_clause,[],[f59,f124,f101])).

fof(f59,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_waybel_7(sK0,sK1,X2)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f122,plain,
    ( ~ spl7_1
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f60,f120,f101])).

fof(f60,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f118,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f61,f116,f101])).

fof(f61,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f114,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f62,f112,f101])).

fof(f62,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f63,f108,f101])).

fof(f63,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f64,f104,f101])).

fof(f64,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
