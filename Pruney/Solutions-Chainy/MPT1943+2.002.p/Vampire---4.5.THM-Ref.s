%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 505 expanded)
%              Number of leaves         :   30 ( 205 expanded)
%              Depth                    :   20
%              Number of atoms          : 1320 (2393 expanded)
%              Number of equality atoms :    5 (  17 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f610,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f123,f128,f138,f141,f170,f181,f203,f208,f241,f270,f275,f318,f322,f559,f600,f609])).

fof(f609,plain,
    ( spl7_9
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | spl7_9
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f607,f127])).

fof(f127,plain,
    ( ~ r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_9
  <=> r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f607,plain,
    ( r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))
    | ~ spl7_18
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f605,f269])).

fof(f269,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl7_24
  <=> m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f605,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))
    | ~ spl7_18
    | ~ spl7_44 ),
    inference(resolution,[],[f599,f213])).

fof(f213,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),X4),X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k10_yellow_6(sK0,sK1),X4) )
    | ~ spl7_18 ),
    inference(resolution,[],[f207,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK6(X0,X1,X2),X2)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

% (10663)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f207,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl7_18
  <=> m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f599,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK2))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl7_44
  <=> r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f600,plain,
    ( spl7_44
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f563,f556,f311,f267,f229,f200,f178,f167,f82,f77,f72,f597])).

fof(f72,plain,
    ( spl7_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f77,plain,
    ( spl7_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f82,plain,
    ( spl7_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f167,plain,
    ( spl7_15
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f178,plain,
    ( spl7_16
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f200,plain,
    ( spl7_17
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f229,plain,
    ( spl7_19
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f311,plain,
    ( spl7_26
  <=> m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f556,plain,
    ( spl7_42
  <=> sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f563,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK2))
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_24
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f561,f312])).

fof(f312,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f311])).

fof(f561,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0))
    | r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK2))
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(resolution,[],[f558,f287])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ sP4(X0,sK2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f286,f74])).

fof(f74,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f286,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK2,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f285,f202])).

fof(f202,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK2,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_19
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f284,f180])).

fof(f180,plain,
    ( v7_waybel_0(sK2)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f178])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK2,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_19
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f283,f230])).

fof(f230,plain,
    ( v4_orders_2(sK2)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f229])).

fof(f283,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK2,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f282,f169])).

fof(f169,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f167])).

fof(f282,plain,
    ( ! [X0] :
        ( v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK2,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f281,f84])).

fof(f84,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK2,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl7_5
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f276,f79])).

fof(f79,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v7_waybel_0(sK2)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP4(X0,sK2,sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK2)) )
    | ~ spl7_24 ),
    inference(resolution,[],[f269,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f558,plain,
    ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f556])).

fof(f559,plain,
    ( spl7_42
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | spl7_15
    | ~ spl7_17
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f554,f315,f200,f167,f135,f120,f87,f72,f67,f62,f57,f556])).

fof(f57,plain,
    ( spl7_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f62,plain,
    ( spl7_2
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f67,plain,
    ( spl7_3
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f87,plain,
    ( spl7_7
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f120,plain,
    ( spl7_8
  <=> m2_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f135,plain,
    ( spl7_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f315,plain,
    ( spl7_27
  <=> sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f554,plain,
    ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | spl7_15
    | ~ spl7_17
    | ~ spl7_27 ),
    inference(duplicate_literal_removal,[],[f553])).

fof(f553,plain,
    ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0)
    | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | spl7_15
    | ~ spl7_17
    | ~ spl7_27 ),
    inference(resolution,[],[f548,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X3))
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f548,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK2,sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))
        | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | spl7_15
    | ~ spl7_17
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f547,f169])).

fof(f547,plain,
    ( ! [X0] :
        ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0)
        | v2_struct_0(sK2)
        | r1_waybel_0(sK0,sK2,sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_17
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f546,f202])).

fof(f546,plain,
    ( ! [X0] :
        ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0)
        | ~ l1_waybel_0(sK2,sK0)
        | v2_struct_0(sK2)
        | r1_waybel_0(sK0,sK2,sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_27 ),
    inference(resolution,[],[f539,f171])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | r1_waybel_0(sK0,X0,X1) )
    | spl7_4
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f117,f136])).

fof(f136,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
        | r1_waybel_0(sK0,X0,X1) )
    | spl7_4 ),
    inference(resolution,[],[f74,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).

fof(f539,plain,
    ( ! [X0] :
        ( ~ r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))))
        | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_27 ),
    inference(resolution,[],[f476,f122])).

fof(f122,plain,
    ( m2_yellow_6(sK2,sK0,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f476,plain,
    ( ! [X2,X1] :
        ( ~ m2_yellow_6(X2,sK0,sK1)
        | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X1,sK0)
        | ~ r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X1,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f475,f136])).

fof(f475,plain,
    ( ! [X2,X1] :
        ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X1,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1)
        | ~ r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X1,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))))
        | ~ l1_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f474,f89])).

fof(f89,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f474,plain,
    ( ! [X2,X1] :
        ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X1,sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1)
        | ~ r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X1,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))))
        | ~ l1_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f473,f74])).

fof(f473,plain,
    ( ! [X2,X1] :
        ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X1,sK0)
        | v2_struct_0(sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m2_yellow_6(X2,sK0,sK1)
        | ~ r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X1,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))))
        | ~ l1_struct_0(sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_27 ),
    inference(resolution,[],[f330,f106])).

fof(f106,plain,
    ( ! [X6,X4,X5] :
        ( r2_waybel_0(X4,sK1,X6)
        | v2_struct_0(X4)
        | ~ l1_waybel_0(sK1,X4)
        | ~ m2_yellow_6(X5,X4,sK1)
        | ~ r2_waybel_0(X4,X5,X6)
        | ~ l1_struct_0(X4) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f105,f64])).

fof(f64,plain,
    ( v4_orders_2(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f105,plain,
    ( ! [X6,X4,X5] :
        ( ~ l1_struct_0(X4)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X4)
        | ~ l1_waybel_0(sK1,X4)
        | ~ m2_yellow_6(X5,X4,sK1)
        | ~ r2_waybel_0(X4,X5,X6)
        | r2_waybel_0(X4,sK1,X6) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f95,f59])).

fof(f59,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f95,plain,
    ( ! [X6,X4,X5] :
        ( ~ l1_struct_0(X4)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X4)
        | ~ l1_waybel_0(sK1,X4)
        | ~ m2_yellow_6(X5,X4,sK1)
        | ~ r2_waybel_0(X4,X5,X6)
        | r2_waybel_0(X4,sK1,X6) )
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ r2_waybel_0(X0,X2,X3)
      | r2_waybel_0(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X2,X3) )
              | ~ m2_yellow_6(X2,X0,X1) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m2_yellow_6(X2,X0,X1)
             => ! [X3] :
                  ( r2_waybel_0(X0,X2,X3)
                 => r2_waybel_0(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).

fof(f69,plain,
    ( v7_waybel_0(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f330,plain,
    ( ! [X0] :
        ( ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))))
        | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0) )
    | spl7_1
    | spl7_4
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f329,f59])).

fof(f329,plain,
    ( ! [X0] :
        ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0)
        | ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))))
        | v2_struct_0(sK1) )
    | spl7_4
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f326,f89])).

fof(f326,plain,
    ( ! [X0] :
        ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))))
        | v2_struct_0(sK1) )
    | spl7_4
    | ~ spl7_11
    | ~ spl7_27 ),
    inference(resolution,[],[f325,f174])).

fof(f174,plain,
    ( ! [X2,X3] :
        ( ~ r1_waybel_0(sK0,X2,X3)
        | ~ l1_waybel_0(X2,sK0)
        | ~ r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),X3))
        | v2_struct_0(X2) )
    | spl7_4
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f118,f136])).

fof(f118,plain,
    ( ! [X2,X3] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | ~ r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),X3))
        | ~ r1_waybel_0(sK0,X2,X3) )
    | spl7_4 ),
    inference(resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f325,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))
        | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0) )
    | ~ spl7_27 ),
    inference(resolution,[],[f324,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( m1_connsp_2(sK5(X0,X1,X3),X0,X3)
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))
        | r1_waybel_0(sK0,sK1,X0) )
    | ~ spl7_27 ),
    inference(resolution,[],[f317,f37])).

fof(f37,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r1_waybel_0(X0,X1,X4)
      | ~ m1_connsp_2(X4,X0,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f317,plain,
    ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK1,sK0)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f315])).

fof(f322,plain,
    ( spl7_9
    | ~ spl7_18
    | ~ spl7_24
    | spl7_26 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl7_9
    | ~ spl7_18
    | ~ spl7_24
    | spl7_26 ),
    inference(subsumption_resolution,[],[f320,f127])).

fof(f320,plain,
    ( r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))
    | ~ spl7_18
    | ~ spl7_24
    | spl7_26 ),
    inference(subsumption_resolution,[],[f319,f269])).

fof(f319,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))
    | ~ spl7_18
    | spl7_26 ),
    inference(resolution,[],[f313,f211])).

fof(f211,plain,
    ( ! [X2] :
        ( m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k10_yellow_6(sK0,sK1),X2) )
    | ~ spl7_18 ),
    inference(resolution,[],[f207,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK6(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f313,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f311])).

fof(f318,plain,
    ( ~ spl7_26
    | spl7_27
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_18
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f295,f272,f205,f87,f82,f77,f72,f67,f62,f57,f315,f311])).

fof(f272,plain,
    ( spl7_25
  <=> r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f295,plain,
    ( sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK1,sK0)
    | ~ m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_18
    | ~ spl7_25 ),
    inference(resolution,[],[f274,f227])).

fof(f227,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k10_yellow_6(sK0,sK1))
        | sP4(X1,sK1,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f226,f74])).

fof(f226,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f225,f89])).

fof(f225,plain,
    ( ! [X1] :
        ( ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f224,f69])).

fof(f224,plain,
    ( ! [X1] :
        ( ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f223,f64])).

fof(f223,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | spl7_1
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f222,f59])).

fof(f222,plain,
    ( ! [X1] :
        ( v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f221,f84])).

fof(f221,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl7_5
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f210,f79])).

fof(f210,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v7_waybel_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sP4(X1,sK1,sK0)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) )
    | ~ spl7_18 ),
    inference(resolution,[],[f207,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP4(X3,X1,X0)
      | ~ r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f274,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK1))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f272])).

fof(f275,plain,
    ( ~ spl7_24
    | spl7_25
    | spl7_9
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f243,f205,f125,f272,f267])).

fof(f243,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK1))
    | ~ m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_9
    | ~ spl7_18 ),
    inference(resolution,[],[f212,f127])).

fof(f212,plain,
    ( ! [X3] :
        ( r1_tarski(k10_yellow_6(sK0,sK1),X3)
        | r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),X3),k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_18 ),
    inference(resolution,[],[f207,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f270,plain,
    ( spl7_24
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f265,f229,f200,f178,f167,f82,f77,f72,f267])).

fof(f265,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f264,f202])).

fof(f264,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f263,f74])).

fof(f263,plain,
    ( v2_struct_0(sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5
    | ~ spl7_6
    | spl7_15
    | ~ spl7_16
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f262,f84])).

fof(f262,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK2,sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5
    | spl7_15
    | ~ spl7_16
    | ~ spl7_19 ),
    inference(resolution,[],[f261,f79])).

fof(f261,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(sK2,X7)
        | m1_subset_1(k10_yellow_6(X7,sK2),k1_zfmisc_1(u1_struct_0(X7))) )
    | spl7_15
    | ~ spl7_16
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f193,f230])).

fof(f193,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ v4_orders_2(sK2)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(sK2,X7)
        | m1_subset_1(k10_yellow_6(X7,sK2),k1_zfmisc_1(u1_struct_0(X7))) )
    | spl7_15
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f185,f169])).

fof(f185,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(sK2)
        | ~ v4_orders_2(sK2)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(sK2,X7)
        | m1_subset_1(k10_yellow_6(X7,sK2),k1_zfmisc_1(u1_struct_0(X7))) )
    | ~ spl7_16 ),
    inference(resolution,[],[f180,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f241,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | spl7_19 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | spl7_19 ),
    inference(subsumption_resolution,[],[f239,f136])).

fof(f239,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | spl7_19 ),
    inference(subsumption_resolution,[],[f238,f74])).

fof(f238,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_8
    | spl7_19 ),
    inference(subsumption_resolution,[],[f237,f89])).

fof(f237,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8
    | spl7_19 ),
    inference(resolution,[],[f236,f122])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(sK2,X0,sK1)
        | ~ l1_waybel_0(sK1,X0)
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_19 ),
    inference(resolution,[],[f231,f112])).

fof(f112,plain,
    ( ! [X10,X11] :
        ( v4_orders_2(X11)
        | v2_struct_0(X10)
        | ~ l1_waybel_0(sK1,X10)
        | ~ m2_yellow_6(X11,X10,sK1)
        | ~ l1_struct_0(X10) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f111,f64])).

fof(f111,plain,
    ( ! [X10,X11] :
        ( ~ l1_struct_0(X10)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X10)
        | ~ l1_waybel_0(sK1,X10)
        | ~ m2_yellow_6(X11,X10,sK1)
        | v4_orders_2(X11) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f98,f59])).

fof(f98,plain,
    ( ! [X10,X11] :
        ( ~ l1_struct_0(X10)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X10)
        | ~ l1_waybel_0(sK1,X10)
        | ~ m2_yellow_6(X11,X10,sK1)
        | v4_orders_2(X11) )
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | v4_orders_2(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
          | ~ m2_yellow_6(X2,X0,X1) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_yellow_6(X2,X0,X1)
         => ( l1_waybel_0(X2,X0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

fof(f231,plain,
    ( ~ v4_orders_2(sK2)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f229])).

fof(f208,plain,
    ( spl7_18
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f165,f87,f82,f77,f72,f67,f62,f57,f205])).

fof(f165,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f164,f89])).

fof(f164,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f163,f74])).

fof(f163,plain,
    ( v2_struct_0(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f162,f84])).

fof(f162,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_waybel_0(sK1,sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(resolution,[],[f108,f79])).

fof(f108,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(sK1,X7)
        | m1_subset_1(k10_yellow_6(X7,sK1),k1_zfmisc_1(u1_struct_0(X7))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f107,f64])).

fof(f107,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(sK1,X7)
        | m1_subset_1(k10_yellow_6(X7,sK1),k1_zfmisc_1(u1_struct_0(X7))) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f96,f59])).

fof(f96,plain,
    ( ! [X7] :
        ( ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X7)
        | ~ l1_waybel_0(sK1,X7)
        | m1_subset_1(k10_yellow_6(X7,sK1),k1_zfmisc_1(u1_struct_0(X7))) )
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f49])).

fof(f203,plain,
    ( spl7_17
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f198,f135,f120,f87,f72,f67,f62,f57,f200])).

fof(f198,plain,
    ( l1_waybel_0(sK2,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(resolution,[],[f146,f122])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(X0,sK0,sK1)
        | l1_waybel_0(X0,sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f145,f136])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | ~ m2_yellow_6(X0,sK0,sK1)
        | l1_waybel_0(X0,sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f144,f74])).

fof(f144,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ m2_yellow_6(X0,sK0,sK1)
        | l1_waybel_0(X0,sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(resolution,[],[f116,f89])).

fof(f116,plain,
    ( ! [X14,X15] :
        ( ~ l1_waybel_0(sK1,X14)
        | v2_struct_0(X14)
        | ~ l1_struct_0(X14)
        | ~ m2_yellow_6(X15,X14,sK1)
        | l1_waybel_0(X15,X14) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f115,f64])).

fof(f115,plain,
    ( ! [X14,X15] :
        ( ~ l1_struct_0(X14)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(sK1,X14)
        | ~ m2_yellow_6(X15,X14,sK1)
        | l1_waybel_0(X15,X14) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f100,f59])).

fof(f100,plain,
    ( ! [X14,X15] :
        ( ~ l1_struct_0(X14)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X14)
        | ~ l1_waybel_0(sK1,X14)
        | ~ m2_yellow_6(X15,X14,sK1)
        | l1_waybel_0(X15,X14) )
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | l1_waybel_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f181,plain,
    ( spl7_16
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f176,f135,f120,f87,f72,f67,f62,f57,f178])).

fof(f176,plain,
    ( v7_waybel_0(sK2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(resolution,[],[f175,f122])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(X0,sK0,sK1)
        | v7_waybel_0(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f143,f136])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | ~ m2_yellow_6(X0,sK0,sK1)
        | v7_waybel_0(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f142,f74])).

fof(f142,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ m2_yellow_6(X0,sK0,sK1)
        | v7_waybel_0(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(resolution,[],[f114,f89])).

fof(f114,plain,
    ( ! [X12,X13] :
        ( ~ l1_waybel_0(sK1,X12)
        | v2_struct_0(X12)
        | ~ l1_struct_0(X12)
        | ~ m2_yellow_6(X13,X12,sK1)
        | v7_waybel_0(X13) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f113,f64])).

fof(f113,plain,
    ( ! [X12,X13] :
        ( ~ l1_struct_0(X12)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X12)
        | ~ l1_waybel_0(sK1,X12)
        | ~ m2_yellow_6(X13,X12,sK1)
        | v7_waybel_0(X13) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f99,f59])).

fof(f99,plain,
    ( ! [X12,X13] :
        ( ~ l1_struct_0(X12)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X12)
        | ~ l1_waybel_0(sK1,X12)
        | ~ m2_yellow_6(X13,X12,sK1)
        | v7_waybel_0(X13) )
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | v7_waybel_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f170,plain,
    ( ~ spl7_15
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f147,f132,f120,f167])).

fof(f132,plain,
    ( spl7_10
  <=> ! [X0] :
        ( ~ m2_yellow_6(X0,sK0,sK1)
        | ~ v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f147,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(resolution,[],[f133,f122])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ m2_yellow_6(X0,sK0,sK1)
        | ~ v2_struct_0(X0) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f141,plain,
    ( ~ spl7_6
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl7_6
    | spl7_11 ),
    inference(subsumption_resolution,[],[f139,f84])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_11 ),
    inference(resolution,[],[f137,f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f137,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f138,plain,
    ( spl7_10
    | ~ spl7_11
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f130,f87,f72,f67,f62,f57,f135,f132])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | ~ m2_yellow_6(X0,sK0,sK1)
        | ~ v2_struct_0(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f129,f74])).

fof(f129,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l1_struct_0(sK0)
        | ~ m2_yellow_6(X0,sK0,sK1)
        | ~ v2_struct_0(X0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(resolution,[],[f110,f89])).

fof(f110,plain,
    ( ! [X8,X9] :
        ( ~ l1_waybel_0(sK1,X8)
        | v2_struct_0(X8)
        | ~ l1_struct_0(X8)
        | ~ m2_yellow_6(X9,X8,sK1)
        | ~ v2_struct_0(X9) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f109,f64])).

fof(f109,plain,
    ( ! [X8,X9] :
        ( ~ l1_struct_0(X8)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X8)
        | ~ l1_waybel_0(sK1,X8)
        | ~ m2_yellow_6(X9,X8,sK1)
        | ~ v2_struct_0(X9) )
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f97,f59])).

fof(f97,plain,
    ( ! [X8,X9] :
        ( ~ l1_struct_0(X8)
        | v2_struct_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(X8)
        | ~ l1_waybel_0(sK1,X8)
        | ~ m2_yellow_6(X9,X8,sK1)
        | ~ v2_struct_0(X9) )
    | ~ spl7_3 ),
    inference(resolution,[],[f69,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m2_yellow_6(X2,X0,X1)
      | ~ v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f128,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f26,f125])).

fof(f26,plain,(
    ~ r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2))
              & m2_yellow_6(X2,X0,X1) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m2_yellow_6(X2,X0,X1)
               => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
              ( m2_yellow_6(X2,X0,X1)
             => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_yellow_6)).

fof(f123,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f25,f120])).

fof(f25,plain,(
    m2_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f90,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f30,f87])).

fof(f30,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f85,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f75,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (10658)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (10670)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (10662)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (10669)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (10655)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (10658)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (10673)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (10655)Refutation not found, incomplete strategy% (10655)------------------------------
% 0.20/0.47  % (10655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f610,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f123,f128,f138,f141,f170,f181,f203,f208,f241,f270,f275,f318,f322,f559,f600,f609])).
% 0.20/0.48  fof(f609,plain,(
% 0.20/0.48    spl7_9 | ~spl7_18 | ~spl7_24 | ~spl7_44),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f608])).
% 0.20/0.48  fof(f608,plain,(
% 0.20/0.48    $false | (spl7_9 | ~spl7_18 | ~spl7_24 | ~spl7_44)),
% 0.20/0.48    inference(subsumption_resolution,[],[f607,f127])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ~r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) | spl7_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f125])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    spl7_9 <=> r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.48  fof(f607,plain,(
% 0.20/0.48    r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) | (~spl7_18 | ~spl7_24 | ~spl7_44)),
% 0.20/0.48    inference(subsumption_resolution,[],[f605,f269])).
% 0.20/0.48  fof(f269,plain,(
% 0.20/0.48    m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_24),
% 0.20/0.48    inference(avatar_component_clause,[],[f267])).
% 0.20/0.48  fof(f267,plain,(
% 0.20/0.48    spl7_24 <=> m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.48  fof(f605,plain,(
% 0.20/0.48    ~m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) | (~spl7_18 | ~spl7_44)),
% 0.20/0.48    inference(resolution,[],[f599,f213])).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k10_yellow_6(sK0,sK1),X4)) ) | ~spl7_18),
% 0.20/0.48    inference(resolution,[],[f207,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK6(X0,X1,X2),X2) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  % (10663)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f205])).
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    spl7_18 <=> m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.48  fof(f599,plain,(
% 0.20/0.48    r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK2)) | ~spl7_44),
% 0.20/0.48    inference(avatar_component_clause,[],[f597])).
% 0.20/0.48  fof(f597,plain,(
% 0.20/0.48    spl7_44 <=> r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.20/0.48  fof(f600,plain,(
% 0.20/0.48    spl7_44 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_19 | ~spl7_24 | ~spl7_26 | ~spl7_42),
% 0.20/0.48    inference(avatar_split_clause,[],[f563,f556,f311,f267,f229,f200,f178,f167,f82,f77,f72,f597])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl7_4 <=> v2_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl7_5 <=> v2_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl7_6 <=> l1_pre_topc(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    spl7_15 <=> v2_struct_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    spl7_16 <=> v7_waybel_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    spl7_17 <=> l1_waybel_0(sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    spl7_19 <=> v4_orders_2(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.48  fof(f311,plain,(
% 0.20/0.48    spl7_26 <=> m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.20/0.48  fof(f556,plain,(
% 0.20/0.48    spl7_42 <=> sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.20/0.48  fof(f563,plain,(
% 0.20/0.48    r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK2)) | (spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_19 | ~spl7_24 | ~spl7_26 | ~spl7_42)),
% 0.20/0.48    inference(subsumption_resolution,[],[f561,f312])).
% 0.20/0.48  fof(f312,plain,(
% 0.20/0.48    m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0)) | ~spl7_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f311])).
% 0.20/0.48  fof(f561,plain,(
% 0.20/0.48    ~m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0)) | r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK2)) | (spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_19 | ~spl7_24 | ~spl7_42)),
% 0.20/0.48    inference(resolution,[],[f558,f287])).
% 0.20/0.48  fof(f287,plain,(
% 0.20/0.48    ( ! [X0] : (~sP4(X0,sK2,sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_19 | ~spl7_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f286,f74])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ~v2_struct_0(sK0) | spl7_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f72])).
% 0.20/0.48  fof(f286,plain,(
% 0.20/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~sP4(X0,sK2,sK0) | r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_19 | ~spl7_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f285,f202])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    l1_waybel_0(sK2,sK0) | ~spl7_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f200])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~sP4(X0,sK2,sK0) | r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_19 | ~spl7_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f284,f180])).
% 0.20/0.48  fof(f180,plain,(
% 0.20/0.48    v7_waybel_0(sK2) | ~spl7_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f178])).
% 0.20/0.48  fof(f284,plain,(
% 0.20/0.48    ( ! [X0] : (~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~sP4(X0,sK2,sK0) | r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_19 | ~spl7_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f283,f230])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    v4_orders_2(sK2) | ~spl7_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f229])).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    ( ! [X0] : (~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~sP4(X0,sK2,sK0) | r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f282,f169])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    ~v2_struct_0(sK2) | spl7_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f167])).
% 0.20/0.48  fof(f282,plain,(
% 0.20/0.48    ( ! [X0] : (v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~sP4(X0,sK2,sK0) | r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (~spl7_5 | ~spl7_6 | ~spl7_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f281,f84])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    l1_pre_topc(sK0) | ~spl7_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f82])).
% 0.20/0.48  fof(f281,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~sP4(X0,sK2,sK0) | r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | (~spl7_5 | ~spl7_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f276,f79])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    v2_pre_topc(sK0) | ~spl7_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f77])).
% 0.20/0.48  fof(f276,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | ~v7_waybel_0(sK2) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~sP4(X0,sK2,sK0) | r2_hidden(X0,k10_yellow_6(sK0,sK2))) ) | ~spl7_24),
% 0.20/0.48    inference(resolution,[],[f269,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~sP4(X3,X1,X0) | r2_hidden(X3,k10_yellow_6(X0,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k10_yellow_6(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).
% 0.20/0.48  fof(f558,plain,(
% 0.20/0.48    sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0) | ~spl7_42),
% 0.20/0.48    inference(avatar_component_clause,[],[f556])).
% 0.20/0.48  fof(f559,plain,(
% 0.20/0.48    spl7_42 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11 | spl7_15 | ~spl7_17 | ~spl7_27),
% 0.20/0.48    inference(avatar_split_clause,[],[f554,f315,f200,f167,f135,f120,f87,f72,f67,f62,f57,f556])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl7_1 <=> v2_struct_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl7_2 <=> v4_orders_2(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl7_3 <=> v7_waybel_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl7_7 <=> l1_waybel_0(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl7_8 <=> m2_yellow_6(sK2,sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    spl7_11 <=> l1_struct_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.48  fof(f315,plain,(
% 0.20/0.48    spl7_27 <=> sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.20/0.48  fof(f554,plain,(
% 0.20/0.48    sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11 | spl7_15 | ~spl7_17 | ~spl7_27)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f553])).
% 0.20/0.48  fof(f553,plain,(
% 0.20/0.48    sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0) | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK2,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11 | spl7_15 | ~spl7_17 | ~spl7_27)),
% 0.20/0.48    inference(resolution,[],[f548,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~r1_waybel_0(X0,X1,sK5(X0,X1,X3)) | sP4(X3,X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f548,plain,(
% 0.20/0.48    ( ! [X0] : (r1_waybel_0(sK0,sK2,sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))) | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11 | spl7_15 | ~spl7_17 | ~spl7_27)),
% 0.20/0.48    inference(subsumption_resolution,[],[f547,f169])).
% 0.20/0.48  fof(f547,plain,(
% 0.20/0.48    ( ! [X0] : (sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0) | v2_struct_0(sK2) | r1_waybel_0(sK0,sK2,sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11 | ~spl7_17 | ~spl7_27)),
% 0.20/0.48    inference(subsumption_resolution,[],[f546,f202])).
% 0.20/0.48  fof(f546,plain,(
% 0.20/0.48    ( ! [X0] : (sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | r1_waybel_0(sK0,sK2,sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11 | ~spl7_27)),
% 0.20/0.48    inference(resolution,[],[f539,f171])).
% 0.20/0.48  fof(f171,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,X1)) ) | (spl7_4 | ~spl7_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f117,f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    l1_struct_0(sK0) | ~spl7_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f135])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_struct_0(sK0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | r2_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | r1_waybel_0(sK0,X0,X1)) ) | spl7_4),
% 0.20/0.48    inference(resolution,[],[f74,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | r1_waybel_0(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).
% 0.20/0.48  fof(f539,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11 | ~spl7_27)),
% 0.20/0.48    inference(resolution,[],[f476,f122])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    m2_yellow_6(sK2,sK0,sK1) | ~spl7_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f120])).
% 0.20/0.48  fof(f476,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~m2_yellow_6(X2,sK0,sK1) | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X1,sK0) | ~r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X1,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_11 | ~spl7_27)),
% 0.20/0.48    inference(subsumption_resolution,[],[f475,f136])).
% 0.20/0.48  fof(f475,plain,(
% 0.20/0.48    ( ! [X2,X1] : (sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X1,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X1,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) | ~l1_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_11 | ~spl7_27)),
% 0.20/0.48    inference(subsumption_resolution,[],[f474,f89])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    l1_waybel_0(sK1,sK0) | ~spl7_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f87])).
% 0.20/0.48  fof(f474,plain,(
% 0.20/0.48    ( ! [X2,X1] : (sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X1,sK0) | ~l1_waybel_0(sK1,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X1,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) | ~l1_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_11 | ~spl7_27)),
% 0.20/0.48    inference(subsumption_resolution,[],[f473,f74])).
% 0.20/0.48  fof(f473,plain,(
% 0.20/0.48    ( ! [X2,X1] : (sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X1,sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m2_yellow_6(X2,sK0,sK1) | ~r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X1,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) | ~l1_struct_0(sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_11 | ~spl7_27)),
% 0.20/0.48    inference(resolution,[],[f330,f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ( ! [X6,X4,X5] : (r2_waybel_0(X4,sK1,X6) | v2_struct_0(X4) | ~l1_waybel_0(sK1,X4) | ~m2_yellow_6(X5,X4,sK1) | ~r2_waybel_0(X4,X5,X6) | ~l1_struct_0(X4)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f105,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    v4_orders_2(sK1) | ~spl7_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f62])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ( ! [X6,X4,X5] : (~l1_struct_0(X4) | ~v4_orders_2(sK1) | v2_struct_0(X4) | ~l1_waybel_0(sK1,X4) | ~m2_yellow_6(X5,X4,sK1) | ~r2_waybel_0(X4,X5,X6) | r2_waybel_0(X4,sK1,X6)) ) | (spl7_1 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f95,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ~v2_struct_0(sK1) | spl7_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f57])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ( ! [X6,X4,X5] : (~l1_struct_0(X4) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X4) | ~l1_waybel_0(sK1,X4) | ~m2_yellow_6(X5,X4,sK1) | ~r2_waybel_0(X4,X5,X6) | r2_waybel_0(X4,sK1,X6)) ) | ~spl7_3),
% 0.20/0.48    inference(resolution,[],[f69,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | ~r2_waybel_0(X0,X2,X3) | r2_waybel_0(X0,X1,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X2,X3)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => ! [X3] : (r2_waybel_0(X0,X2,X3) => r2_waybel_0(X0,X1,X3)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow_6)).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    v7_waybel_0(sK1) | ~spl7_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f67])).
% 0.20/0.48  fof(f330,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0)) ) | (spl7_1 | spl7_4 | ~spl7_7 | ~spl7_11 | ~spl7_27)),
% 0.20/0.48    inference(subsumption_resolution,[],[f329,f59])).
% 0.20/0.48  fof(f329,plain,(
% 0.20/0.48    ( ! [X0] : (sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0) | ~r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) | v2_struct_0(sK1)) ) | (spl7_4 | ~spl7_7 | ~spl7_11 | ~spl7_27)),
% 0.20/0.48    inference(subsumption_resolution,[],[f326,f89])).
% 0.20/0.48  fof(f326,plain,(
% 0.20/0.48    ( ! [X0] : (sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0) | ~l1_waybel_0(sK1,sK0) | ~r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))))) | v2_struct_0(sK1)) ) | (spl7_4 | ~spl7_11 | ~spl7_27)),
% 0.20/0.48    inference(resolution,[],[f325,f174])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~r1_waybel_0(sK0,X2,X3) | ~l1_waybel_0(X2,sK0) | ~r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),X3)) | v2_struct_0(X2)) ) | (spl7_4 | ~spl7_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f118,f136])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~l1_struct_0(sK0) | v2_struct_0(X2) | ~l1_waybel_0(X2,sK0) | ~r2_waybel_0(sK0,X2,k6_subset_1(u1_struct_0(sK0),X3)) | ~r1_waybel_0(sK0,X2,X3)) ) | spl7_4),
% 0.20/0.48    inference(resolution,[],[f74,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f325,plain,(
% 0.20/0.48    ( ! [X0] : (r1_waybel_0(sK0,sK1,sK5(sK0,X0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)))) | sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),X0,sK0)) ) | ~spl7_27),
% 0.20/0.48    inference(resolution,[],[f324,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (m1_connsp_2(sK5(X0,X1,X3),X0,X3) | sP4(X3,X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f324,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))) | r1_waybel_0(sK0,sK1,X0)) ) | ~spl7_27),
% 0.20/0.48    inference(resolution,[],[f317,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X4,X0,X3,X1] : (~sP4(X3,X1,X0) | r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f317,plain,(
% 0.20/0.48    sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK1,sK0) | ~spl7_27),
% 0.20/0.48    inference(avatar_component_clause,[],[f315])).
% 0.20/0.48  fof(f322,plain,(
% 0.20/0.48    spl7_9 | ~spl7_18 | ~spl7_24 | spl7_26),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f321])).
% 0.20/0.48  fof(f321,plain,(
% 0.20/0.48    $false | (spl7_9 | ~spl7_18 | ~spl7_24 | spl7_26)),
% 0.20/0.48    inference(subsumption_resolution,[],[f320,f127])).
% 0.20/0.48  fof(f320,plain,(
% 0.20/0.48    r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) | (~spl7_18 | ~spl7_24 | spl7_26)),
% 0.20/0.48    inference(subsumption_resolution,[],[f319,f269])).
% 0.20/0.48  fof(f319,plain,(
% 0.20/0.48    ~m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)) | (~spl7_18 | spl7_26)),
% 0.20/0.48    inference(resolution,[],[f313,f211])).
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    ( ! [X2] : (m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),X2),u1_struct_0(sK0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k10_yellow_6(sK0,sK1),X2)) ) | ~spl7_18),
% 0.20/0.48    inference(resolution,[],[f207,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK6(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f313,plain,(
% 0.20/0.48    ~m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0)) | spl7_26),
% 0.20/0.48    inference(avatar_component_clause,[],[f311])).
% 0.20/0.48  fof(f318,plain,(
% 0.20/0.48    ~spl7_26 | spl7_27 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_18 | ~spl7_25),
% 0.20/0.48    inference(avatar_split_clause,[],[f295,f272,f205,f87,f82,f77,f72,f67,f62,f57,f315,f311])).
% 0.20/0.48  fof(f272,plain,(
% 0.20/0.48    spl7_25 <=> r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.20/0.48  fof(f295,plain,(
% 0.20/0.48    sP4(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),sK1,sK0) | ~m1_subset_1(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),u1_struct_0(sK0)) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_18 | ~spl7_25)),
% 0.20/0.48    inference(resolution,[],[f274,f227])).
% 0.20/0.48  fof(f227,plain,(
% 0.20/0.48    ( ! [X1] : (~r2_hidden(X1,k10_yellow_6(sK0,sK1)) | sP4(X1,sK1,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f226,f74])).
% 0.20/0.48  fof(f226,plain,(
% 0.20/0.48    ( ! [X1] : (v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sP4(X1,sK1,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f225,f89])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    ( ! [X1] : (~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sP4(X1,sK1,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f224,f69])).
% 0.20/0.48  fof(f224,plain,(
% 0.20/0.48    ( ! [X1] : (~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sP4(X1,sK1,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) ) | (spl7_1 | ~spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f223,f64])).
% 0.20/0.48  fof(f223,plain,(
% 0.20/0.48    ( ! [X1] : (~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sP4(X1,sK1,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) ) | (spl7_1 | ~spl7_5 | ~spl7_6 | ~spl7_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f222,f59])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    ( ! [X1] : (v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sP4(X1,sK1,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) ) | (~spl7_5 | ~spl7_6 | ~spl7_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f221,f84])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sP4(X1,sK1,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) ) | (~spl7_5 | ~spl7_18)),
% 0.20/0.48    inference(subsumption_resolution,[],[f210,f79])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | ~v7_waybel_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sP4(X1,sK1,sK0) | ~r2_hidden(X1,k10_yellow_6(sK0,sK1))) ) | ~spl7_18),
% 0.20/0.48    inference(resolution,[],[f207,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | sP4(X3,X1,X0) | ~r2_hidden(X3,k10_yellow_6(X0,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k10_yellow_6(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f274,plain,(
% 0.20/0.48    r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK1)) | ~spl7_25),
% 0.20/0.48    inference(avatar_component_clause,[],[f272])).
% 0.20/0.48  fof(f275,plain,(
% 0.20/0.48    ~spl7_24 | spl7_25 | spl7_9 | ~spl7_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f243,f205,f125,f272,f267])).
% 0.20/0.48  fof(f243,plain,(
% 0.20/0.48    r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2)),k10_yellow_6(sK0,sK1)) | ~m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_9 | ~spl7_18)),
% 0.20/0.48    inference(resolution,[],[f212,f127])).
% 0.20/0.48  fof(f212,plain,(
% 0.20/0.48    ( ! [X3] : (r1_tarski(k10_yellow_6(sK0,sK1),X3) | r2_hidden(sK6(u1_struct_0(sK0),k10_yellow_6(sK0,sK1),X3),k10_yellow_6(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_18),
% 0.20/0.48    inference(resolution,[],[f207,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK6(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f270,plain,(
% 0.20/0.48    spl7_24 | spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_19),
% 0.20/0.48    inference(avatar_split_clause,[],[f265,f229,f200,f178,f167,f82,f77,f72,f267])).
% 0.20/0.48  fof(f265,plain,(
% 0.20/0.48    m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_17 | ~spl7_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f264,f202])).
% 0.20/0.48  fof(f264,plain,(
% 0.20/0.48    ~l1_waybel_0(sK2,sK0) | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_4 | ~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f263,f74])).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~l1_waybel_0(sK2,sK0) | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_5 | ~spl7_6 | spl7_15 | ~spl7_16 | ~spl7_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f262,f84])).
% 0.20/0.48  fof(f262,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK2,sK0) | m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_5 | spl7_15 | ~spl7_16 | ~spl7_19)),
% 0.20/0.48    inference(resolution,[],[f261,f79])).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    ( ! [X7] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(X7) | ~l1_waybel_0(sK2,X7) | m1_subset_1(k10_yellow_6(X7,sK2),k1_zfmisc_1(u1_struct_0(X7)))) ) | (spl7_15 | ~spl7_16 | ~spl7_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f193,f230])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    ( ! [X7] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~v4_orders_2(sK2) | v2_struct_0(X7) | ~l1_waybel_0(sK2,X7) | m1_subset_1(k10_yellow_6(X7,sK2),k1_zfmisc_1(u1_struct_0(X7)))) ) | (spl7_15 | ~spl7_16)),
% 0.20/0.48    inference(subsumption_resolution,[],[f185,f169])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    ( ! [X7] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(X7) | ~l1_waybel_0(sK2,X7) | m1_subset_1(k10_yellow_6(X7,sK2),k1_zfmisc_1(u1_struct_0(X7)))) ) | ~spl7_16),
% 0.20/0.48    inference(resolution,[],[f180,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v7_waybel_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 0.20/0.48  fof(f241,plain,(
% 0.20/0.48    spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11 | spl7_19),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f240])).
% 0.20/0.48  fof(f240,plain,(
% 0.20/0.48    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11 | spl7_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f239,f136])).
% 0.20/0.48  fof(f239,plain,(
% 0.20/0.48    ~l1_struct_0(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | spl7_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f238,f74])).
% 0.20/0.48  fof(f238,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~l1_struct_0(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_8 | spl7_19)),
% 0.20/0.48    inference(subsumption_resolution,[],[f237,f89])).
% 0.20/0.48  fof(f237,plain,(
% 0.20/0.48    ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_8 | spl7_19)),
% 0.20/0.48    inference(resolution,[],[f236,f122])).
% 0.20/0.48  fof(f236,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_yellow_6(sK2,X0,sK1) | ~l1_waybel_0(sK1,X0) | v2_struct_0(X0) | ~l1_struct_0(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_19)),
% 0.20/0.48    inference(resolution,[],[f231,f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ( ! [X10,X11] : (v4_orders_2(X11) | v2_struct_0(X10) | ~l1_waybel_0(sK1,X10) | ~m2_yellow_6(X11,X10,sK1) | ~l1_struct_0(X10)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f111,f64])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X10,X11] : (~l1_struct_0(X10) | ~v4_orders_2(sK1) | v2_struct_0(X10) | ~l1_waybel_0(sK1,X10) | ~m2_yellow_6(X11,X10,sK1) | v4_orders_2(X11)) ) | (spl7_1 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f98,f59])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X10,X11] : (~l1_struct_0(X10) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X10) | ~l1_waybel_0(sK1,X10) | ~m2_yellow_6(X11,X10,sK1) | v4_orders_2(X11)) ) | ~spl7_3),
% 0.20/0.48    inference(resolution,[],[f69,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | v4_orders_2(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) | ~m2_yellow_6(X2,X0,X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    ~v4_orders_2(sK2) | spl7_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f229])).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    spl7_18 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f165,f87,f82,f77,f72,f67,f62,f57,f205])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f164,f89])).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    ~l1_waybel_0(sK1,sK0) | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.48    inference(subsumption_resolution,[],[f163,f74])).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_6)),
% 0.20/0.48    inference(subsumption_resolution,[],[f162,f84])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.20/0.48    inference(resolution,[],[f108,f79])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    ( ! [X7] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(X7) | ~l1_waybel_0(sK1,X7) | m1_subset_1(k10_yellow_6(X7,sK1),k1_zfmisc_1(u1_struct_0(X7)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f107,f64])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ( ! [X7] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | ~v4_orders_2(sK1) | v2_struct_0(X7) | ~l1_waybel_0(sK1,X7) | m1_subset_1(k10_yellow_6(X7,sK1),k1_zfmisc_1(u1_struct_0(X7)))) ) | (spl7_1 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f96,f59])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ( ! [X7] : (~v2_pre_topc(X7) | ~l1_pre_topc(X7) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X7) | ~l1_waybel_0(sK1,X7) | m1_subset_1(k10_yellow_6(X7,sK1),k1_zfmisc_1(u1_struct_0(X7)))) ) | ~spl7_3),
% 0.20/0.48    inference(resolution,[],[f69,f49])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    spl7_17 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f198,f135,f120,f87,f72,f67,f62,f57,f200])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    l1_waybel_0(sK2,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11)),
% 0.20/0.48    inference(resolution,[],[f146,f122])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | l1_waybel_0(X0,sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f145,f136])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(sK0) | ~m2_yellow_6(X0,sK0,sK1) | l1_waybel_0(X0,sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f144,f74])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m2_yellow_6(X0,sK0,sK1) | l1_waybel_0(X0,sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_7)),
% 0.20/0.48    inference(resolution,[],[f116,f89])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ( ! [X14,X15] : (~l1_waybel_0(sK1,X14) | v2_struct_0(X14) | ~l1_struct_0(X14) | ~m2_yellow_6(X15,X14,sK1) | l1_waybel_0(X15,X14)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f115,f64])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ( ! [X14,X15] : (~l1_struct_0(X14) | ~v4_orders_2(sK1) | v2_struct_0(X14) | ~l1_waybel_0(sK1,X14) | ~m2_yellow_6(X15,X14,sK1) | l1_waybel_0(X15,X14)) ) | (spl7_1 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f100,f59])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ( ! [X14,X15] : (~l1_struct_0(X14) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X14) | ~l1_waybel_0(sK1,X14) | ~m2_yellow_6(X15,X14,sK1) | l1_waybel_0(X15,X14)) ) | ~spl7_3),
% 0.20/0.48    inference(resolution,[],[f69,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | l1_waybel_0(X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f181,plain,(
% 0.20/0.48    spl7_16 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f176,f135,f120,f87,f72,f67,f62,f57,f178])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    v7_waybel_0(sK2) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_11)),
% 0.20/0.48    inference(resolution,[],[f175,f122])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | v7_waybel_0(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7 | ~spl7_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f143,f136])).
% 0.20/0.48  fof(f143,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(sK0) | ~m2_yellow_6(X0,sK0,sK1) | v7_waybel_0(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f142,f74])).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m2_yellow_6(X0,sK0,sK1) | v7_waybel_0(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_7)),
% 0.20/0.48    inference(resolution,[],[f114,f89])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ( ! [X12,X13] : (~l1_waybel_0(sK1,X12) | v2_struct_0(X12) | ~l1_struct_0(X12) | ~m2_yellow_6(X13,X12,sK1) | v7_waybel_0(X13)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f113,f64])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ( ! [X12,X13] : (~l1_struct_0(X12) | ~v4_orders_2(sK1) | v2_struct_0(X12) | ~l1_waybel_0(sK1,X12) | ~m2_yellow_6(X13,X12,sK1) | v7_waybel_0(X13)) ) | (spl7_1 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f99,f59])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X12,X13] : (~l1_struct_0(X12) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X12) | ~l1_waybel_0(sK1,X12) | ~m2_yellow_6(X13,X12,sK1) | v7_waybel_0(X13)) ) | ~spl7_3),
% 0.20/0.48    inference(resolution,[],[f69,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | v7_waybel_0(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    ~spl7_15 | ~spl7_8 | ~spl7_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f147,f132,f120,f167])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    spl7_10 <=> ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | ~v2_struct_0(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.48  fof(f147,plain,(
% 0.20/0.48    ~v2_struct_0(sK2) | (~spl7_8 | ~spl7_10)),
% 0.20/0.48    inference(resolution,[],[f133,f122])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    ( ! [X0] : (~m2_yellow_6(X0,sK0,sK1) | ~v2_struct_0(X0)) ) | ~spl7_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f132])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ~spl7_6 | spl7_11),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    $false | (~spl7_6 | spl7_11)),
% 0.20/0.48    inference(subsumption_resolution,[],[f139,f84])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | spl7_11),
% 0.20/0.48    inference(resolution,[],[f137,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    ~l1_struct_0(sK0) | spl7_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f135])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    spl7_10 | ~spl7_11 | spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f130,f87,f72,f67,f62,f57,f135,f132])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(sK0) | ~m2_yellow_6(X0,sK0,sK1) | ~v2_struct_0(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f129,f74])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~l1_struct_0(sK0) | ~m2_yellow_6(X0,sK0,sK1) | ~v2_struct_0(X0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_7)),
% 0.20/0.48    inference(resolution,[],[f110,f89])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    ( ! [X8,X9] : (~l1_waybel_0(sK1,X8) | v2_struct_0(X8) | ~l1_struct_0(X8) | ~m2_yellow_6(X9,X8,sK1) | ~v2_struct_0(X9)) ) | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f109,f64])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ( ! [X8,X9] : (~l1_struct_0(X8) | ~v4_orders_2(sK1) | v2_struct_0(X8) | ~l1_waybel_0(sK1,X8) | ~m2_yellow_6(X9,X8,sK1) | ~v2_struct_0(X9)) ) | (spl7_1 | ~spl7_3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f97,f59])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X8,X9] : (~l1_struct_0(X8) | v2_struct_0(sK1) | ~v4_orders_2(sK1) | v2_struct_0(X8) | ~l1_waybel_0(sK1,X8) | ~m2_yellow_6(X9,X8,sK1) | ~v2_struct_0(X9)) ) | ~spl7_3),
% 0.20/0.48    inference(resolution,[],[f69,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v7_waybel_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m2_yellow_6(X2,X0,X1) | ~v2_struct_0(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ~spl7_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f26,f125])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ~r1_tarski(k10_yellow_6(sK0,sK1),k10_yellow_6(sK0,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)) & m2_yellow_6(X2,X0,X1)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m2_yellow_6(X2,X0,X1) => r1_tarski(k10_yellow_6(X0,X1),k10_yellow_6(X0,X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_yellow_6)).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl7_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f120])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    m2_yellow_6(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl7_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f87])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    l1_waybel_0(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl7_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f82])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl7_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f77])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ~spl7_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f31,f72])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl7_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f67])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v7_waybel_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl7_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f62])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    v4_orders_2(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ~spl7_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f57])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ~v2_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (10658)------------------------------
% 0.20/0.48  % (10658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (10658)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (10658)Memory used [KB]: 10874
% 0.20/0.48  % (10658)Time elapsed: 0.066 s
% 0.20/0.48  % (10658)------------------------------
% 0.20/0.48  % (10658)------------------------------
% 0.20/0.48  % (10661)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (10653)Success in time 0.132 s
%------------------------------------------------------------------------------
