%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t34_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:51 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :  412 ( 922 expanded)
%              Number of leaves         :   85 ( 371 expanded)
%              Depth                    :   23
%              Number of atoms          : 2509 (4453 expanded)
%              Number of equality atoms :   10 (  64 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f774,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f149,f156,f163,f176,f183,f190,f197,f204,f211,f215,f220,f225,f243,f258,f279,f286,f316,f331,f345,f356,f361,f404,f423,f430,f437,f445,f471,f484,f544,f565,f581,f590,f596,f604,f612,f618,f623,f631,f637,f700,f725,f731,f737,f748,f762,f766,f773])).

fof(f773,plain,
    ( spl7_89
    | ~ spl7_90
    | ~ spl7_92
    | ~ spl7_94
    | spl7_97
    | ~ spl7_102 ),
    inference(avatar_contradiction_clause,[],[f772])).

fof(f772,plain,
    ( $false
    | ~ spl7_89
    | ~ spl7_90
    | ~ spl7_92
    | ~ spl7_94
    | ~ spl7_97
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f771,f699])).

fof(f699,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_89 ),
    inference(avatar_component_clause,[],[f698])).

fof(f698,plain,
    ( spl7_89
  <=> ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f771,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_90
    | ~ spl7_92
    | ~ spl7_94
    | ~ spl7_97
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f770,f715])).

fof(f715,plain,
    ( v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f714])).

fof(f714,plain,
    ( spl7_94
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f770,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_90
    | ~ spl7_92
    | ~ spl7_97
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f769,f709])).

fof(f709,plain,
    ( v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_92 ),
    inference(avatar_component_clause,[],[f708])).

fof(f708,plain,
    ( spl7_92
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f769,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_90
    | ~ spl7_97
    | ~ spl7_102 ),
    inference(subsumption_resolution,[],[f767,f703])).

fof(f703,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl7_90
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f767,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_97
    | ~ spl7_102 ),
    inference(resolution,[],[f765,f724])).

fof(f724,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ spl7_97 ),
    inference(avatar_component_clause,[],[f723])).

fof(f723,plain,
    ( spl7_97
  <=> ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f765,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK0,X0),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | ~ spl7_102 ),
    inference(avatar_component_clause,[],[f764])).

fof(f764,plain,
    ( spl7_102
  <=> ! [X0] :
        ( m1_subset_1(sK5(sK0,X0),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f766,plain,
    ( ~ spl7_7
    | spl7_102
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f634,f241,f161,f154,f147,f764,f168])).

fof(f168,plain,
    ( spl7_7
  <=> ~ v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f147,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f154,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f161,plain,
    ( spl7_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f241,plain,
    ( spl7_26
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f634,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK0,X0),k2_struct_0(sK0))
        | ~ v1_compts_1(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f633,f148])).

fof(f148,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f633,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK0,X0),k2_struct_0(sK0))
        | ~ v1_compts_1(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f632,f162])).

fof(f162,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f632,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK0,X0),k2_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f289,f155])).

fof(f155,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f154])).

fof(f289,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK0,X0),k2_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v1_compts_1(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_26 ),
    inference(superposition,[],[f139,f242])).

fof(f242,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f241])).

fof(f139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
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
    inference(flattening,[],[f87])).

fof(f87,plain,(
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
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',l37_yellow19)).

fof(f762,plain,
    ( ~ spl7_99
    | ~ spl7_101
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | spl7_33
    | ~ spl7_40
    | spl7_55
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f692,f412,f406,f354,f277,f209,f195,f188,f181,f174,f760,f754])).

fof(f754,plain,
    ( spl7_99
  <=> ~ v2_struct_0(k3_yellow19(sK6,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f760,plain,
    ( spl7_101
  <=> ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f174,plain,
    ( spl7_9
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f181,plain,
    ( spl7_10
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f188,plain,
    ( spl7_12
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f195,plain,
    ( spl7_14
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f209,plain,
    ( spl7_18
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f277,plain,
    ( spl7_33
  <=> ~ v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f354,plain,
    ( spl7_40
  <=> k2_struct_0(sK6) = u1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f406,plain,
    ( spl7_55
  <=> ~ v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f412,plain,
    ( spl7_56
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f692,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK6)))
    | ~ v2_struct_0(k3_yellow19(sK6,k2_struct_0(sK0),sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33
    | ~ spl7_40
    | ~ spl7_55
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f691,f407])).

fof(f407,plain,
    ( ~ v2_struct_0(sK6)
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f406])).

fof(f691,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK6)))
    | v2_struct_0(sK6)
    | ~ v2_struct_0(k3_yellow19(sK6,k2_struct_0(sK0),sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33
    | ~ spl7_40
    | ~ spl7_56 ),
    inference(subsumption_resolution,[],[f687,f413])).

fof(f413,plain,
    ( l1_struct_0(sK6)
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f412])).

fof(f687,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK6)))
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK6)
    | ~ v2_struct_0(k3_yellow19(sK6,k2_struct_0(sK0),sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33
    | ~ spl7_40 ),
    inference(superposition,[],[f655,f355])).

fof(f355,plain,
    ( k2_struct_0(sK6) = u1_struct_0(sK6)
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f354])).

fof(f655,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_struct_0(X1)
        | v2_struct_0(X1)
        | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f654,f189])).

fof(f189,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f188])).

fof(f654,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X1)
        | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f653,f182])).

fof(f182,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f181])).

fof(f653,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X1)
        | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) )
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f652,f196])).

fof(f196,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f195])).

fof(f652,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X1)
        | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) )
    | ~ spl7_9
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f651,f175])).

fof(f175,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f174])).

fof(f651,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
        | v1_xboole_0(sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X1)
        | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) )
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f640,f278])).

fof(f278,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f277])).

fof(f640,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
        | v1_xboole_0(sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X1)
        | ~ v2_struct_0(k3_yellow19(X1,k2_struct_0(sK0),sK1)) )
    | ~ spl7_18 ),
    inference(resolution,[],[f210,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
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
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
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
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',fc5_yellow19)).

fof(f210,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f209])).

fof(f748,plain,
    ( spl7_1
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_30
    | spl7_33
    | ~ spl7_36
    | spl7_91 ),
    inference(avatar_contradiction_clause,[],[f747])).

fof(f747,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_36
    | ~ spl7_91 ),
    inference(subsumption_resolution,[],[f746,f330])).

fof(f330,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl7_36
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f746,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_91 ),
    inference(forward_demodulation,[],[f745,f242])).

fof(f745,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_91 ),
    inference(subsumption_resolution,[],[f744,f148])).

fof(f744,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_91 ),
    inference(subsumption_resolution,[],[f743,f210])).

fof(f743,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_91 ),
    inference(subsumption_resolution,[],[f742,f189])).

fof(f742,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_91 ),
    inference(subsumption_resolution,[],[f741,f182])).

fof(f741,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl7_9
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_91 ),
    inference(subsumption_resolution,[],[f740,f175])).

fof(f740,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_91 ),
    inference(subsumption_resolution,[],[f739,f278])).

fof(f739,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_91 ),
    inference(subsumption_resolution,[],[f738,f269])).

fof(f269,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl7_30
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f738,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl7_91 ),
    inference(resolution,[],[f706,f116])).

fof(f116,plain,(
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
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',dt_k3_yellow19)).

fof(f706,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_91 ),
    inference(avatar_component_clause,[],[f705])).

fof(f705,plain,
    ( spl7_91
  <=> ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f737,plain,
    ( spl7_1
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_30
    | spl7_33
    | ~ spl7_36
    | spl7_95 ),
    inference(avatar_contradiction_clause,[],[f736])).

fof(f736,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_36
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f735,f330])).

fof(f735,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_95 ),
    inference(forward_demodulation,[],[f734,f242])).

fof(f734,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f733,f269])).

fof(f733,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_33
    | ~ spl7_95 ),
    inference(subsumption_resolution,[],[f732,f148])).

fof(f732,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_33
    | ~ spl7_95 ),
    inference(resolution,[],[f718,f659])).

fof(f659,plain,
    ( ! [X2] :
        ( v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
        | v2_struct_0(X2)
        | ~ l1_struct_0(X2) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f658,f189])).

fof(f658,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X2)
        | v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f657,f182])).

fof(f657,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X2)
        | v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1)) )
    | ~ spl7_9
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f656,f175])).

fof(f656,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
        | v1_xboole_0(sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X2)
        | v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1)) )
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f641,f278])).

fof(f641,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
        | v1_xboole_0(sK1)
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X2)
        | v4_orders_2(k3_yellow19(X2,k2_struct_0(sK0),sK1)) )
    | ~ spl7_18 ),
    inference(resolution,[],[f210,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | v4_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',fc4_yellow19)).

fof(f718,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_95 ),
    inference(avatar_component_clause,[],[f717])).

fof(f717,plain,
    ( spl7_95
  <=> ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f731,plain,
    ( spl7_1
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_30
    | spl7_33
    | ~ spl7_36
    | spl7_93 ),
    inference(avatar_contradiction_clause,[],[f730])).

fof(f730,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_36
    | ~ spl7_93 ),
    inference(subsumption_resolution,[],[f729,f330])).

fof(f729,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_93 ),
    inference(forward_demodulation,[],[f728,f242])).

fof(f728,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_33
    | ~ spl7_93 ),
    inference(subsumption_resolution,[],[f727,f269])).

fof(f727,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33
    | ~ spl7_93 ),
    inference(subsumption_resolution,[],[f726,f148])).

fof(f726,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33
    | ~ spl7_93 ),
    inference(resolution,[],[f712,f650])).

fof(f650,plain,
    ( ! [X0] :
        ( v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | v2_struct_0(X0)
        | ~ l1_struct_0(X0) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f649,f189])).

fof(f649,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X0)
        | v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) )
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f648,f182])).

fof(f648,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X0)
        | v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) )
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f647,f196])).

fof(f647,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X0)
        | v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) )
    | ~ spl7_9
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f646,f175])).

fof(f646,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | v1_xboole_0(sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X0)
        | v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) )
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f639,f278])).

fof(f639,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | v1_xboole_0(k2_struct_0(sK0))
        | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | v1_xboole_0(sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | v2_struct_0(X0)
        | v7_waybel_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) )
    | ~ spl7_18 ),
    inference(resolution,[],[f210,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | v2_struct_0(X0)
      | v7_waybel_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f712,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_93 ),
    inference(avatar_component_clause,[],[f711])).

fof(f711,plain,
    ( spl7_93
  <=> ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f725,plain,
    ( ~ spl7_91
    | ~ spl7_93
    | ~ spl7_95
    | spl7_88
    | ~ spl7_97
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f674,f213,f209,f195,f188,f181,f174,f165,f161,f154,f147,f723,f695,f717,f711,f705])).

fof(f695,plain,
    ( spl7_88
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f165,plain,
    ( spl7_6
  <=> v1_compts_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f213,plain,
    ( spl7_20
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,sK1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f674,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f673,f166])).

fof(f166,plain,
    ( v1_compts_1(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f673,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ v1_compts_1(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f672,f148])).

fof(f672,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f671,f155])).

fof(f671,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f670,f210])).

fof(f670,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f669,f189])).

fof(f669,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_compts_1(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f668,f182])).

fof(f668,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
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
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f667,f196])).

fof(f667,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
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
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f666,f175])).

fof(f666,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
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
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f664,f162])).

fof(f664,plain,
    ( ~ m1_subset_1(sK5(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),k2_struct_0(sK0))
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
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(resolution,[],[f230,f336])).

fof(f336,plain,(
    ! [X4,X3] :
      ( r1_waybel_7(X3,X4,sK5(X3,k3_yellow19(X3,k2_struct_0(X3),X4)))
      | ~ l1_pre_topc(X3)
      | v1_xboole_0(X4)
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3))))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3)))))
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ v1_compts_1(X3)
      | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3) ) ),
    inference(subsumption_resolution,[],[f334,f139])).

fof(f334,plain,(
    ! [X4,X3] :
      ( ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v1_xboole_0(X4)
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3))))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3)))))
      | ~ m1_subset_1(sK5(X3,k3_yellow19(X3,k2_struct_0(X3),X4)),u1_struct_0(X3))
      | r1_waybel_7(X3,X4,sK5(X3,k3_yellow19(X3,k2_struct_0(X3),X4)))
      | v2_struct_0(X3)
      | ~ v1_compts_1(X3)
      | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3) ) ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,(
    ! [X4,X3] :
      ( ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | v1_xboole_0(X4)
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(k2_struct_0(X3))))
      | ~ v2_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ v13_waybel_0(X4,k3_yellow_1(k2_struct_0(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X3)))))
      | ~ m1_subset_1(sK5(X3,k3_yellow19(X3,k2_struct_0(X3),X4)),u1_struct_0(X3))
      | r1_waybel_7(X3,X4,sK5(X3,k3_yellow19(X3,k2_struct_0(X3),X4)))
      | v2_struct_0(X3)
      | ~ v2_pre_topc(X3)
      | ~ l1_pre_topc(X3)
      | ~ v1_compts_1(X3)
      | v2_struct_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v4_orders_2(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ v7_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4))
      | ~ l1_waybel_0(k3_yellow19(X3,k2_struct_0(X3),X4),X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f104,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r3_waybel_9(X0,X1,sK5(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_compts_1(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',t17_yellow19)).

fof(f230,plain,
    ( ! [X2] :
        ( ~ r1_waybel_7(sK0,sK1,X2)
        | ~ m1_subset_1(X2,k2_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_20 ),
    inference(backward_demodulation,[],[f228,f214])).

fof(f214,plain,
    ( ! [X2] :
        ( ~ r1_waybel_7(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f228,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f216,f162])).

fof(f216,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f128,f142])).

fof(f142,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',dt_l1_pre_topc)).

fof(f128,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',d3_struct_0)).

fof(f700,plain,
    ( ~ spl7_89
    | spl7_1
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_30
    | spl7_33 ),
    inference(avatar_split_clause,[],[f690,f277,f268,f209,f195,f188,f181,f174,f147,f698])).

fof(f690,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_1
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f689,f148])).

fof(f689,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_30
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f688,f269])).

fof(f688,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(duplicate_literal_removal,[],[f685])).

fof(f685,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_33 ),
    inference(resolution,[],[f655,f110])).

fof(f110,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',dt_k2_struct_0)).

fof(f637,plain,
    ( spl7_6
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_75 ),
    inference(avatar_split_clause,[],[f635,f524,f161,f154,f147,f165])).

fof(f524,plain,
    ( spl7_75
  <=> ~ l1_waybel_0(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f635,plain,
    ( v1_compts_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f593,f148])).

fof(f593,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f592,f162])).

fof(f592,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f591,f155])).

fof(f591,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_75 ),
    inference(resolution,[],[f525,f137])).

fof(f137,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
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
    inference(flattening,[],[f85])).

fof(f85,plain,(
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
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',l38_yellow19)).

fof(f525,plain,
    ( ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ spl7_75 ),
    inference(avatar_component_clause,[],[f524])).

fof(f631,plain,
    ( spl7_1
    | ~ spl7_30
    | ~ spl7_74
    | spl7_77
    | ~ spl7_78 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_30
    | ~ spl7_74
    | ~ spl7_77
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f629,f148])).

fof(f629,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_74
    | ~ spl7_77
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f628,f522])).

fof(f522,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | ~ spl7_74 ),
    inference(avatar_component_clause,[],[f521])).

fof(f521,plain,
    ( spl7_74
  <=> l1_waybel_0(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f628,plain,
    ( ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_77
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f627,f528])).

fof(f528,plain,
    ( ~ v2_struct_0(sK4(sK0))
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl7_77
  <=> ~ v2_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f627,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f624,f269])).

fof(f624,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_78 ),
    inference(resolution,[],[f537,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_yellow19(X0,X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k2_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',fc2_yellow19)).

fof(f537,plain,
    ( v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f536])).

fof(f536,plain,
    ( spl7_78
  <=> v1_xboole_0(k2_yellow19(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f623,plain,
    ( spl7_1
    | ~ spl7_30
    | ~ spl7_74
    | spl7_77
    | spl7_81 ),
    inference(avatar_contradiction_clause,[],[f622])).

fof(f622,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_30
    | ~ spl7_74
    | ~ spl7_77
    | ~ spl7_81 ),
    inference(subsumption_resolution,[],[f528,f621])).

fof(f621,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ spl7_1
    | ~ spl7_30
    | ~ spl7_74
    | ~ spl7_81 ),
    inference(subsumption_resolution,[],[f620,f148])).

fof(f620,plain,
    ( v2_struct_0(sK4(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_74
    | ~ spl7_81 ),
    inference(subsumption_resolution,[],[f619,f522])).

fof(f619,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_81 ),
    inference(subsumption_resolution,[],[f609,f269])).

fof(f609,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_81 ),
    inference(resolution,[],[f543,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f543,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl7_81 ),
    inference(avatar_component_clause,[],[f542])).

fof(f542,plain,
    ( spl7_81
  <=> ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f618,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | ~ spl7_76 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f616,f169])).

fof(f169,plain,
    ( ~ v1_compts_1(sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f168])).

fof(f616,plain,
    ( v1_compts_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f615,f148])).

fof(f615,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f614,f162])).

fof(f614,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_76 ),
    inference(subsumption_resolution,[],[f613,f155])).

fof(f613,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_76 ),
    inference(resolution,[],[f531,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK4(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f531,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ spl7_76 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl7_76
  <=> v2_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f612,plain,
    ( spl7_76
    | spl7_1
    | ~ spl7_30
    | spl7_69
    | ~ spl7_70
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(avatar_split_clause,[],[f608,f521,f515,f509,f506,f268,f147,f530])).

fof(f506,plain,
    ( spl7_69
  <=> ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f509,plain,
    ( spl7_70
  <=> v7_waybel_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f515,plain,
    ( spl7_72
  <=> v4_orders_2(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f608,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ spl7_1
    | ~ spl7_30
    | ~ spl7_69
    | ~ spl7_70
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f607,f148])).

fof(f607,plain,
    ( v2_struct_0(sK4(sK0))
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_69
    | ~ spl7_70
    | ~ spl7_72
    | ~ spl7_74 ),
    inference(subsumption_resolution,[],[f606,f522])).

fof(f606,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_69
    | ~ spl7_70
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f605,f510])).

fof(f510,plain,
    ( v7_waybel_0(sK4(sK0))
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f509])).

fof(f605,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_69
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f598,f516])).

fof(f516,plain,
    ( v4_orders_2(sK4(sK0))
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f515])).

fof(f598,plain,
    ( v2_struct_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f597,f269])).

fof(f597,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK4(sK0))
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_69 ),
    inference(resolution,[],[f507,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) )
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_waybel_0(k2_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',fc3_yellow19)).

fof(f507,plain,
    ( ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f506])).

fof(f604,plain,
    ( spl7_1
    | ~ spl7_30
    | spl7_69
    | ~ spl7_70
    | ~ spl7_72
    | ~ spl7_74
    | spl7_77 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_30
    | ~ spl7_69
    | ~ spl7_70
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f602,f148])).

fof(f602,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_69
    | ~ spl7_70
    | ~ spl7_72
    | ~ spl7_74
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f601,f522])).

fof(f601,plain,
    ( ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_69
    | ~ spl7_70
    | ~ spl7_72
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f600,f510])).

fof(f600,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_69
    | ~ spl7_72
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f599,f516])).

fof(f599,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | v2_struct_0(sK0)
    | ~ spl7_30
    | ~ spl7_69
    | ~ spl7_77 ),
    inference(subsumption_resolution,[],[f598,f528])).

fof(f596,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | spl7_75 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f594,f169])).

fof(f594,plain,
    ( v1_compts_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_75 ),
    inference(subsumption_resolution,[],[f593,f148])).

fof(f590,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | spl7_73 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f588,f169])).

fof(f588,plain,
    ( v1_compts_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f587,f148])).

fof(f587,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f586,f162])).

fof(f586,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_73 ),
    inference(subsumption_resolution,[],[f585,f155])).

fof(f585,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_73 ),
    inference(resolution,[],[f519,f135])).

fof(f135,plain,(
    ! [X0] :
      ( v4_orders_2(sK4(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f519,plain,
    ( ~ v4_orders_2(sK4(sK0))
    | ~ spl7_73 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl7_73
  <=> ~ v4_orders_2(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f581,plain,
    ( spl7_54
    | ~ spl7_83
    | ~ spl7_85
    | spl7_86
    | ~ spl7_16
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f373,f354,f202,f579,f576,f570,f409])).

fof(f409,plain,
    ( spl7_54
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f570,plain,
    ( spl7_83
  <=> ~ v1_compts_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f576,plain,
    ( spl7_85
  <=> ~ v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f579,plain,
    ( spl7_86
  <=> ! [X0] :
        ( m1_subset_1(sK5(sK6,X0),k2_struct_0(sK6))
        | ~ l1_waybel_0(X0,sK6)
        | ~ v7_waybel_0(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f202,plain,
    ( spl7_16
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f373,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK6,X0),k2_struct_0(sK6))
        | ~ v2_pre_topc(sK6)
        | ~ v1_compts_1(sK6)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK6)
        | v2_struct_0(sK6) )
    | ~ spl7_16
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f369,f203])).

fof(f203,plain,
    ( l1_pre_topc(sK6)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f202])).

fof(f369,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK6,X0),k2_struct_0(sK6))
        | ~ v2_pre_topc(sK6)
        | ~ l1_pre_topc(sK6)
        | ~ v1_compts_1(sK6)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK6)
        | v2_struct_0(sK6) )
    | ~ spl7_40 ),
    inference(superposition,[],[f139,f355])).

fof(f565,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | spl7_71 ),
    inference(avatar_contradiction_clause,[],[f564])).

fof(f564,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f563,f169])).

fof(f563,plain,
    ( v1_compts_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f562,f148])).

fof(f562,plain,
    ( v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f561,f162])).

fof(f561,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_2
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f560,f155])).

fof(f560,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_71 ),
    inference(resolution,[],[f513,f136])).

fof(f136,plain,(
    ! [X0] :
      ( v7_waybel_0(sK4(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f513,plain,
    ( ~ v7_waybel_0(sK4(sK0))
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f512])).

fof(f512,plain,
    ( spl7_71
  <=> ~ v7_waybel_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f544,plain,
    ( ~ spl7_69
    | ~ spl7_71
    | ~ spl7_73
    | ~ spl7_75
    | spl7_76
    | spl7_78
    | ~ spl7_81
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f496,f359,f343,f268,f241,f168,f161,f154,f147,f542,f536,f530,f524,f518,f512,f506])).

fof(f343,plain,
    ( spl7_38
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ v1_subset_1(k2_yellow19(sK0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X1))
        | m1_subset_1(sK2(k2_yellow19(sK0,X1)),k2_struct_0(sK0))
        | ~ l1_waybel_0(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f359,plain,
    ( spl7_42
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,X0),sK2(k2_yellow19(sK0,X0)))
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f496,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f495,f349])).

fof(f349,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0) )
    | ~ spl7_1
    | ~ spl7_30
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f348,f148])).

fof(f348,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl7_30
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f347,f269])).

fof(f347,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ l1_struct_0(sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | v2_struct_0(sK0) )
    | ~ spl7_38 ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ l1_waybel_0(X0,sK0)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_38 ),
    inference(resolution,[],[f344,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k2_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f344,plain,
    ( ! [X1] :
        ( ~ v1_subset_1(k2_yellow19(sK0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | v2_struct_0(X1)
        | ~ v2_waybel_0(k2_yellow19(sK0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X1))
        | m1_subset_1(sK2(k2_yellow19(sK0,X1)),k2_struct_0(sK0))
        | ~ l1_waybel_0(X1,sK0) )
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f343])).

fof(f495,plain,
    ( ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),k2_struct_0(sK0))
    | ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(forward_demodulation,[],[f494,f242])).

fof(f494,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f493,f169])).

fof(f493,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),u1_struct_0(sK0))
    | v1_compts_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f492,f148])).

fof(f492,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f491,f162])).

fof(f491,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f489,f155])).

fof(f489,plain,
    ( ~ v13_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_yellow19(sK0,sK4(sK0)))
    | v2_struct_0(sK4(sK0))
    | ~ l1_waybel_0(sK4(sK0),sK0)
    | ~ v4_orders_2(sK4(sK0))
    | ~ v7_waybel_0(sK4(sK0))
    | ~ v2_waybel_0(k2_yellow19(sK0,sK4(sK0)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(k2_yellow19(sK0,sK4(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v1_compts_1(sK0)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(resolution,[],[f452,f133])).

fof(f133,plain,(
    ! [X2,X0] :
      ( ~ r3_waybel_9(X0,sK4(X0),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v1_compts_1(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f452,plain,
    ( ! [X0] :
        ( r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f451,f148])).

fof(f451,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0)))
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_30
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f450,f269])).

fof(f450,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0)))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0)))
        | ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(resolution,[],[f368,f124])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_38
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f367,f344])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),k2_struct_0(sK0))
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(forward_demodulation,[],[f366,f242])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),u1_struct_0(sK0))
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0))) )
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f365,f148])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0))) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f364,f162])).

fof(f364,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0))) )
    | ~ spl7_2
    | ~ spl7_42 ),
    inference(subsumption_resolution,[],[f363,f155])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0))) )
    | ~ spl7_42 ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(sK2(k2_yellow19(sK0,X0)),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r3_waybel_9(sK0,X0,sK2(k2_yellow19(sK0,X0))) )
    | ~ spl7_42 ),
    inference(resolution,[],[f360,f101])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',t12_yellow19)).

fof(f360,plain,
    ( ! [X0] :
        ( r1_waybel_7(sK0,k2_yellow19(sK0,X0),sK2(k2_yellow19(sK0,X0)))
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0) )
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f359])).

fof(f484,plain,
    ( ~ spl7_57
    | spl7_66
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f370,f354,f482,f415])).

fof(f415,plain,
    ( spl7_57
  <=> ~ l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f482,plain,
    ( spl7_66
  <=> m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f370,plain,
    ( m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6)))
    | ~ l1_struct_0(sK6)
    | ~ spl7_40 ),
    inference(superposition,[],[f110,f355])).

fof(f471,plain,
    ( ~ spl7_65
    | spl7_51 ),
    inference(avatar_split_clause,[],[f455,f393,f469])).

fof(f469,plain,
    ( spl7_65
  <=> ~ v1_xboole_0(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f393,plain,
    ( spl7_51
  <=> ~ v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f455,plain,
    ( ~ v1_xboole_0(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl7_51 ),
    inference(resolution,[],[f453,f394])).

fof(f394,plain,
    ( ~ v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f393])).

fof(f453,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f337,f109])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',existence_m1_subset_1)).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK3(k1_zfmisc_1(X0)))
      | v1_xboole_0(sK3(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f231,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',t2_subset)).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK3(k1_zfmisc_1(X1)))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f105,f109])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',t5_subset)).

fof(f445,plain,
    ( ~ spl7_57
    | ~ spl7_63
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f372,f354,f443,f415])).

fof(f443,plain,
    ( spl7_63
  <=> ~ v1_subset_1(k2_struct_0(sK6),k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f372,plain,
    ( ~ v1_subset_1(k2_struct_0(sK6),k2_struct_0(sK6))
    | ~ l1_struct_0(sK6)
    | ~ spl7_40 ),
    inference(superposition,[],[f126,f355])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',fc12_struct_0)).

fof(f437,plain,
    ( ~ spl7_16
    | spl7_57 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_57 ),
    inference(subsumption_resolution,[],[f435,f203])).

fof(f435,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ spl7_57 ),
    inference(resolution,[],[f416,f142])).

fof(f416,plain,
    ( ~ l1_struct_0(sK6)
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f415])).

fof(f430,plain,
    ( ~ spl7_45
    | ~ spl7_47
    | ~ spl7_49
    | spl7_50
    | spl7_60
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f259,f223,f428,f396,f390,f384,f378])).

fof(f378,plain,
    ( spl7_45
  <=> ~ v1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f384,plain,
    ( spl7_47
  <=> ~ v2_waybel_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f390,plain,
    ( spl7_49
  <=> ~ v13_waybel_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f396,plain,
    ( spl7_50
  <=> v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f428,plain,
    ( spl7_60
  <=> r1_waybel_7(sK0,sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),sK2(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f223,plain,
    ( spl7_24
  <=> ! [X1] :
        ( v1_xboole_0(X1)
        | r1_waybel_7(sK0,X1,sK2(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f259,plain,
    ( r1_waybel_7(sK0,sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),sK2(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))))
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl7_24 ),
    inference(resolution,[],[f224,f109])).

fof(f224,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | r1_waybel_7(sK0,X1,sK2(X1))
        | v1_xboole_0(X1)
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f223])).

fof(f423,plain,
    ( spl7_54
    | ~ spl7_57
    | ~ spl7_59
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f371,f354,f421,f415,f409])).

fof(f421,plain,
    ( spl7_59
  <=> ~ v1_xboole_0(k2_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f371,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK6))
    | ~ l1_struct_0(sK6)
    | v2_struct_0(sK6)
    | ~ spl7_40 ),
    inference(superposition,[],[f127,f355])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',fc2_struct_0)).

fof(f404,plain,
    ( ~ spl7_45
    | ~ spl7_47
    | ~ spl7_49
    | spl7_50
    | spl7_52
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f245,f241,f218,f402,f396,f390,f384,f378])).

fof(f402,plain,
    ( spl7_52
  <=> m1_subset_1(sK2(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f218,plain,
    ( spl7_22
  <=> ! [X1] :
        ( v1_xboole_0(X1)
        | m1_subset_1(sK2(X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f245,plain,
    ( m1_subset_1(sK2(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),k2_struct_0(sK0))
    | v1_xboole_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))))
    | ~ v13_waybel_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK3(k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(resolution,[],[f244,f109])).

fof(f244,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | m1_subset_1(sK2(X1),k2_struct_0(sK0))
        | v1_xboole_0(X1)
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f219,f242])).

fof(f219,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | m1_subset_1(sK2(X1),u1_struct_0(sK0))
        | v1_xboole_0(X1)
        | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f218])).

fof(f361,plain,
    ( spl7_42
    | ~ spl7_31
    | spl7_1
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f288,f223,f147,f271,f359])).

fof(f271,plain,
    ( spl7_31
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | r1_waybel_7(sK0,k2_yellow19(sK0,X0),sK2(k2_yellow19(sK0,X0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_1
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f280,f148])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(sK0)
        | r1_waybel_7(sK0,k2_yellow19(sK0,X0),sK2(k2_yellow19(sK0,X0)))
        | v1_xboole_0(k2_yellow19(sK0,X0))
        | ~ v13_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(k2_yellow19(sK0,X0),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(k2_yellow19(sK0,X0),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_24 ),
    inference(resolution,[],[f117,f224])).

fof(f117,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',dt_k2_yellow19)).

fof(f356,plain,
    ( spl7_40
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f229,f202,f354])).

fof(f229,plain,
    ( k2_struct_0(sK6) = u1_struct_0(sK6)
    | ~ spl7_16 ),
    inference(resolution,[],[f216,f203])).

fof(f345,plain,
    ( spl7_38
    | ~ spl7_31
    | spl7_1
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f287,f241,f218,f147,f271,f343])).

fof(f287,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | m1_subset_1(sK2(k2_yellow19(sK0,X1)),k2_struct_0(sK0))
        | v1_xboole_0(k2_yellow19(sK0,X1))
        | ~ v13_waybel_0(k2_yellow19(sK0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(k2_yellow19(sK0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(k2_yellow19(sK0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_1
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f281,f148])).

fof(f281,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | v2_struct_0(sK0)
        | m1_subset_1(sK2(k2_yellow19(sK0,X1)),k2_struct_0(sK0))
        | v1_xboole_0(k2_yellow19(sK0,X1))
        | ~ v13_waybel_0(k2_yellow19(sK0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(k2_yellow19(sK0,X1),k3_yellow_1(k2_struct_0(sK0)))
        | ~ v1_subset_1(k2_yellow19(sK0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) )
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(resolution,[],[f117,f244])).

fof(f331,plain,
    ( ~ spl7_31
    | spl7_36
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f261,f241,f329,f271])).

fof(f261,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl7_26 ),
    inference(superposition,[],[f110,f242])).

fof(f316,plain,
    ( ~ spl7_31
    | ~ spl7_35
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f263,f241,f314,f271])).

fof(f314,plain,
    ( spl7_35
  <=> ~ v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f263,plain,
    ( ~ v1_subset_1(k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl7_26 ),
    inference(superposition,[],[f126,f242])).

fof(f286,plain,
    ( ~ spl7_4
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f284,f162])).

fof(f284,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_31 ),
    inference(resolution,[],[f272,f142])).

fof(f272,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f271])).

fof(f279,plain,
    ( ~ spl7_31
    | ~ spl7_33
    | spl7_1
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f264,f241,f147,f277,f271])).

fof(f264,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | ~ spl7_1
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f262,f148])).

fof(f262,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_26 ),
    inference(superposition,[],[f127,f242])).

fof(f258,plain,
    ( spl7_28
    | spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f251,f241,f218,f209,f195,f188,f181,f174,f256])).

fof(f256,plain,
    ( spl7_28
  <=> m1_subset_1(sK2(sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f251,plain,
    ( m1_subset_1(sK2(sK1),k2_struct_0(sK0))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f250,f196])).

fof(f250,plain,
    ( m1_subset_1(sK2(sK1),k2_struct_0(sK0))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f249,f182])).

fof(f249,plain,
    ( m1_subset_1(sK2(sK1),k2_struct_0(sK0))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl7_9
    | ~ spl7_12
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f248,f189])).

fof(f248,plain,
    ( m1_subset_1(sK2(sK1),k2_struct_0(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl7_9
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(subsumption_resolution,[],[f246,f175])).

fof(f246,plain,
    ( m1_subset_1(sK2(sK1),k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl7_18
    | ~ spl7_22
    | ~ spl7_26 ),
    inference(resolution,[],[f244,f210])).

fof(f243,plain,
    ( spl7_26
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f228,f161,f241])).

fof(f225,plain,
    ( spl7_6
    | spl7_24 ),
    inference(avatar_split_clause,[],[f91,f223,f165])).

fof(f91,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | r1_waybel_7(sK0,X1,sK2(X1))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',t34_yellow19)).

fof(f220,plain,
    ( spl7_6
    | spl7_22 ),
    inference(avatar_split_clause,[],[f90,f218,f165])).

fof(f90,plain,(
    ! [X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | m1_subset_1(sK2(X1),u1_struct_0(sK0))
      | v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f215,plain,
    ( ~ spl7_7
    | spl7_20 ),
    inference(avatar_split_clause,[],[f92,f213,f168])).

fof(f92,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_waybel_7(sK0,sK1,X2)
      | ~ v1_compts_1(sK0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f211,plain,
    ( ~ spl7_7
    | spl7_18 ),
    inference(avatar_split_clause,[],[f97,f209,f168])).

fof(f97,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f204,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f141,f202])).

fof(f141,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t34_yellow19.p',existence_l1_pre_topc)).

fof(f197,plain,
    ( ~ spl7_7
    | spl7_14 ),
    inference(avatar_split_clause,[],[f94,f195,f168])).

fof(f94,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f190,plain,
    ( ~ spl7_7
    | spl7_12 ),
    inference(avatar_split_clause,[],[f96,f188,f168])).

fof(f96,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f183,plain,
    ( ~ spl7_7
    | spl7_10 ),
    inference(avatar_split_clause,[],[f95,f181,f168])).

fof(f95,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f176,plain,
    ( ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f93,f174,f168])).

fof(f93,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f163,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f100,f161])).

fof(f100,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f156,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f99,f154])).

fof(f99,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f149,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f98,f147])).

fof(f98,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
