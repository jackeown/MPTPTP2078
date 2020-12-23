%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1971+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:59 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  457 (1211 expanded)
%              Number of leaves         :   69 ( 534 expanded)
%              Depth                    :   19
%              Number of atoms          : 3169 (8507 expanded)
%              Number of equality atoms :   60 (  98 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2617,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f170,f171,f174,f177,f183,f186,f189,f195,f200,f205,f215,f220,f225,f273,f278,f283,f359,f427,f455,f465,f484,f566,f611,f626,f636,f649,f730,f762,f777,f833,f843,f1009,f1021,f1228,f1251,f1286,f1499,f1515,f1525,f1535,f1555,f1583,f1625,f1691,f1709,f1740,f1806,f2086,f2113,f2236,f2421,f2603,f2604,f2612])).

fof(f2612,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | spl6_9
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f2611])).

fof(f2611,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | spl6_9
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f2610,f199])).

fof(f199,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl6_10
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f2610,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_9 ),
    inference(subsumption_resolution,[],[f2609,f136])).

fof(f136,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_1
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f2609,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl6_4
    | spl6_9 ),
    inference(subsumption_resolution,[],[f2605,f148])).

fof(f148,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2605,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | spl6_9 ),
    inference(resolution,[],[f169,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_yellow_7)).

fof(f169,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl6_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f2604,plain,
    ( spl6_26
    | ~ spl6_120
    | ~ spl6_176
    | ~ spl6_191 ),
    inference(avatar_split_clause,[],[f2589,f2418,f2234,f1737,f548])).

fof(f548,plain,
    ( spl6_26
  <=> r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f1737,plain,
    ( spl6_120
  <=> m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f2234,plain,
    ( spl6_176
  <=> ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_176])])).

fof(f2418,plain,
    ( spl6_191
  <=> r2_hidden(k12_lattice3(sK0,sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_191])])).

fof(f2589,plain,
    ( r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ spl6_120
    | ~ spl6_176
    | ~ spl6_191 ),
    inference(subsumption_resolution,[],[f2586,f1739])).

fof(f1739,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_120 ),
    inference(avatar_component_clause,[],[f1737])).

fof(f2586,plain,
    ( ~ m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ spl6_176
    | ~ spl6_191 ),
    inference(resolution,[],[f2420,f2235])).

fof(f2235,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl6_176 ),
    inference(avatar_component_clause,[],[f2234])).

fof(f2420,plain,
    ( r2_hidden(k12_lattice3(sK0,sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ spl6_191 ),
    inference(avatar_component_clause,[],[f2418])).

fof(f2603,plain,
    ( ~ spl6_9
    | ~ spl6_26
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f2602,f511,f507,f280,f275,f270,f163,f159,f155,f151,f548,f167])).

fof(f151,plain,
    ( spl6_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f155,plain,
    ( spl6_6
  <=> v2_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f159,plain,
    ( spl6_7
  <=> v13_waybel_0(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f163,plain,
    ( spl6_8
  <=> v2_waybel_7(sK1,k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f270,plain,
    ( spl6_16
  <=> v4_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f275,plain,
    ( spl6_17
  <=> v5_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f280,plain,
    ( spl6_18
  <=> v3_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f507,plain,
    ( spl6_21
  <=> v1_lattice3(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f511,plain,
    ( spl6_22
  <=> l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f2602,plain,
    ( ~ r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2601,f282])).

fof(f282,plain,
    ( v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f280])).

fof(f2601,plain,
    ( ~ r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2600,f272])).

fof(f272,plain,
    ( v4_orders_2(k7_lattice3(sK0))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f270])).

fof(f2600,plain,
    ( ~ r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2599,f277])).

fof(f277,plain,
    ( v5_orders_2(k7_lattice3(sK0))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f275])).

fof(f2599,plain,
    ( ~ r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2598,f508])).

fof(f508,plain,
    ( v1_lattice3(k7_lattice3(sK0))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f507])).

fof(f2598,plain,
    ( ~ r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2597,f512])).

fof(f512,plain,
    ( l1_orders_2(k7_lattice3(sK0))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f511])).

fof(f2597,plain,
    ( ~ r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8 ),
    inference(subsumption_resolution,[],[f2596,f152])).

fof(f152,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f151])).

fof(f2596,plain,
    ( ~ r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8 ),
    inference(subsumption_resolution,[],[f2595,f156])).

fof(f156,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f155])).

fof(f2595,plain,
    ( ~ r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_7
    | spl6_8 ),
    inference(subsumption_resolution,[],[f1504,f160])).

fof(f160,plain,
    ( v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f1504,plain,
    ( ~ r2_hidden(sK2(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_8 ),
    inference(resolution,[],[f165,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & ~ r2_hidden(sK2(X0,X1),X1)
                & r2_hidden(k13_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f56,f58,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK2(X0,X1),X1)
            & r2_hidden(k13_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(k13_lattice3(X0,sK2(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(k13_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_7)).

fof(f165,plain,
    ( ~ v2_waybel_7(sK1,k7_lattice3(sK0))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f2421,plain,
    ( spl6_191
    | ~ spl6_25
    | ~ spl6_145 ),
    inference(avatar_split_clause,[],[f2414,f1959,f537,f2418])).

fof(f537,plain,
    ( spl6_25
  <=> r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f1959,plain,
    ( spl6_145
  <=> k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_145])])).

fof(f2414,plain,
    ( r2_hidden(k12_lattice3(sK0,sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ spl6_25
    | ~ spl6_145 ),
    inference(superposition,[],[f539,f1961])).

fof(f1961,plain,
    ( k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1))
    | ~ spl6_145 ),
    inference(avatar_component_clause,[],[f1959])).

fof(f539,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f537])).

fof(f2236,plain,
    ( spl6_176
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(avatar_split_clause,[],[f2232,f1803,f1581,f222,f217,f212,f202,f197,f147,f143,f139,f135,f2234])).

fof(f139,plain,
    ( spl6_2
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f143,plain,
    ( spl6_3
  <=> v1_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f202,plain,
    ( spl6_11
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f212,plain,
    ( spl6_13
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f217,plain,
    ( spl6_14
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f222,plain,
    ( spl6_15
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1581,plain,
    ( spl6_103
  <=> ! [X3,X2] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k12_lattice3(X3,X2,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(X3))
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ v1_waybel_7(sK1,X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v12_waybel_0(sK1,X3)
        | ~ v1_waybel_0(sK1,X3)
        | ~ l1_orders_2(X3)
        | ~ v2_lattice3(X3)
        | ~ v5_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v3_orders_2(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f1803,plain,
    ( spl6_128
  <=> m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f2232,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f2231,f224])).

fof(f224,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f222])).

fof(f2231,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f2230,f219])).

fof(f219,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f217])).

fof(f2230,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f2229,f214])).

fof(f214,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f212])).

fof(f2229,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f2228,f199])).

fof(f2228,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(X0,sK1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f2227,f136])).

fof(f2227,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_waybel_0(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | r2_hidden(X0,sK1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f2226,f140])).

fof(f140,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f139])).

fof(f2226,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v12_waybel_0(sK1,sK0)
        | ~ v1_waybel_0(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | r2_hidden(X0,sK1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f2225,f148])).

fof(f2225,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(sK1,sK0)
        | ~ v1_waybel_0(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | r2_hidden(X0,sK1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f2224,f144])).

fof(f144,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f2224,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(sK1,sK0)
        | ~ v1_waybel_0(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | r2_hidden(X0,sK1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_11
    | ~ spl6_103
    | ~ spl6_128 ),
    inference(subsumption_resolution,[],[f2223,f1805])).

fof(f1805,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_128 ),
    inference(avatar_component_clause,[],[f1803])).

fof(f2223,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k12_lattice3(sK0,X0,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_waybel_7(sK1,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(sK1,sK0)
        | ~ v1_waybel_0(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | r2_hidden(X0,sK1)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_11
    | ~ spl6_103 ),
    inference(resolution,[],[f1582,f204])).

fof(f204,plain,
    ( v2_lattice3(sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f202])).

fof(f1582,plain,
    ( ! [X2,X3] :
        ( ~ v2_lattice3(X3)
        | ~ r2_hidden(k12_lattice3(X3,X2,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(X3))
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ v1_waybel_7(sK1,X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v12_waybel_0(sK1,X3)
        | ~ v1_waybel_0(sK1,X3)
        | ~ l1_orders_2(X3)
        | r2_hidden(X2,sK1)
        | ~ v5_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v3_orders_2(X3) )
    | ~ spl6_103 ),
    inference(avatar_component_clause,[],[f1581])).

fof(f2113,plain,
    ( spl6_145
    | ~ spl6_23
    | ~ spl6_108
    | ~ spl6_161 ),
    inference(avatar_split_clause,[],[f2112,f2084,f1622,f515,f1959])).

fof(f515,plain,
    ( spl6_23
  <=> m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f1622,plain,
    ( spl6_108
  <=> sK2(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK2(k7_lattice3(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f2084,plain,
    ( spl6_161
  <=> ! [X1] :
        ( k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,k9_lattice3(sK0,X1),sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_161])])).

fof(f2112,plain,
    ( k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1))
    | ~ spl6_23
    | ~ spl6_108
    | ~ spl6_161 ),
    inference(forward_demodulation,[],[f2098,f1624])).

fof(f1624,plain,
    ( sK2(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK2(k7_lattice3(sK0),sK1))
    | ~ spl6_108 ),
    inference(avatar_component_clause,[],[f1622])).

fof(f2098,plain,
    ( k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,k9_lattice3(sK0,sK2(k7_lattice3(sK0),sK1)),sK3(k7_lattice3(sK0),sK1))
    | ~ spl6_23
    | ~ spl6_161 ),
    inference(resolution,[],[f2085,f517])).

fof(f517,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f515])).

fof(f2085,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,k9_lattice3(sK0,X1),sK3(k7_lattice3(sK0),sK1)) )
    | ~ spl6_161 ),
    inference(avatar_component_clause,[],[f2084])).

fof(f2086,plain,
    ( spl6_161
    | ~ spl6_116
    | ~ spl6_118 ),
    inference(avatar_split_clause,[],[f2082,f1707,f1688,f2084])).

fof(f1688,plain,
    ( spl6_116
  <=> sK3(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_116])])).

fof(f1707,plain,
    ( spl6_118
  <=> ! [X1] :
        ( k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))) = k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f2082,plain,
    ( ! [X1] :
        ( k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1)) = k12_lattice3(sK0,k9_lattice3(sK0,X1),sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0))) )
    | ~ spl6_116
    | ~ spl6_118 ),
    inference(forward_demodulation,[],[f1708,f1690])).

fof(f1690,plain,
    ( sK3(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))
    | ~ spl6_116 ),
    inference(avatar_component_clause,[],[f1688])).

fof(f1708,plain,
    ( ! [X1] :
        ( k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))) = k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0))) )
    | ~ spl6_118 ),
    inference(avatar_component_clause,[],[f1707])).

fof(f1806,plain,
    ( spl6_128
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_116 ),
    inference(avatar_split_clause,[],[f1801,f1688,f526,f197,f1803])).

fof(f526,plain,
    ( spl6_24
  <=> m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f1801,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_10
    | ~ spl6_24
    | ~ spl6_116 ),
    inference(subsumption_resolution,[],[f1800,f199])).

fof(f1800,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_24
    | ~ spl6_116 ),
    inference(subsumption_resolution,[],[f1797,f528])).

fof(f528,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f526])).

fof(f1797,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl6_116 ),
    inference(superposition,[],[f128,f1690])).

fof(f128,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k9_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_lattice3)).

fof(f1740,plain,
    ( spl6_120
    | ~ spl6_10
    | ~ spl6_23
    | ~ spl6_108 ),
    inference(avatar_split_clause,[],[f1735,f1622,f515,f197,f1737])).

fof(f1735,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_10
    | ~ spl6_23
    | ~ spl6_108 ),
    inference(subsumption_resolution,[],[f1734,f199])).

fof(f1734,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_23
    | ~ spl6_108 ),
    inference(subsumption_resolution,[],[f1731,f517])).

fof(f1731,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl6_108 ),
    inference(superposition,[],[f128,f1624])).

fof(f1709,plain,
    ( spl6_118
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f1705,f526,f222,f217,f212,f202,f197,f1707])).

fof(f1705,plain,
    ( ! [X1] :
        ( k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))) = k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0))) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1704,f224])).

fof(f1704,plain,
    ( ! [X1] :
        ( k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))) = k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ v3_orders_2(sK0) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1703,f219])).

fof(f1703,plain,
    ( ! [X1] :
        ( k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))) = k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1702,f214])).

fof(f1702,plain,
    ( ! [X1] :
        ( k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))) = k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1701,f204])).

fof(f1701,plain,
    ( ! [X1] :
        ( k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))) = k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1657,f199])).

fof(f1657,plain,
    ( ! [X1] :
        ( k12_lattice3(sK0,k9_lattice3(sK0,X1),k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))) = k13_lattice3(k7_lattice3(sK0),X1,sK3(k7_lattice3(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_24 ),
    inference(resolution,[],[f528,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k7_lattice3(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k7_lattice3(X0)))
             => k12_lattice3(X0,k9_lattice3(X0,X1),k9_lattice3(X0,X2)) = k13_lattice3(k7_lattice3(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_7)).

fof(f1691,plain,
    ( spl6_116
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f1686,f526,f197,f1688])).

fof(f1686,plain,
    ( sK3(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))
    | ~ spl6_10
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f1654,f199])).

fof(f1654,plain,
    ( sK3(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK3(k7_lattice3(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | ~ spl6_24 ),
    inference(resolution,[],[f528,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k9_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k7_lattice3(X0)))
         => k9_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_lattice3)).

fof(f1625,plain,
    ( spl6_108
    | ~ spl6_10
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f1620,f515,f197,f1622])).

fof(f1620,plain,
    ( sK2(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK2(k7_lattice3(sK0),sK1))
    | ~ spl6_10
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f1588,f199])).

fof(f1588,plain,
    ( sK2(k7_lattice3(sK0),sK1) = k9_lattice3(sK0,sK2(k7_lattice3(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | ~ spl6_23 ),
    inference(resolution,[],[f517,f129])).

fof(f1583,plain,
    ( spl6_103
    | spl6_5
    | spl6_27 ),
    inference(avatar_split_clause,[],[f1579,f559,f151,f1581])).

fof(f559,plain,
    ( spl6_27
  <=> r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1579,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k12_lattice3(X3,X2,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(X3))
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ v1_waybel_7(sK1,X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v12_waybel_0(sK1,X3)
        | ~ v1_waybel_0(sK1,X3)
        | ~ l1_orders_2(X3)
        | ~ v2_lattice3(X3)
        | ~ v5_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v3_orders_2(X3) )
    | spl6_5
    | spl6_27 ),
    inference(subsumption_resolution,[],[f1571,f152])).

fof(f1571,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,sK1)
        | ~ r2_hidden(k12_lattice3(X3,X2,sK3(k7_lattice3(sK0),sK1)),sK1)
        | ~ m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(X3))
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ v1_waybel_7(sK1,X3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v12_waybel_0(sK1,X3)
        | ~ v1_waybel_0(sK1,X3)
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(X3)
        | ~ v2_lattice3(X3)
        | ~ v5_orders_2(X3)
        | ~ v4_orders_2(X3)
        | ~ v3_orders_2(X3) )
    | spl6_27 ),
    inference(resolution,[],[f561,f115])).

fof(f115,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK5(X0,X1),X1)
                & ~ r2_hidden(sK4(X0,X1),X1)
                & r2_hidden(k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f65,f67,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK4(X0,X1),X1)
            & r2_hidden(k12_lattice3(X0,sK4(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(k12_lattice3(X0,sK4(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_waybel_7)).

fof(f561,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f559])).

fof(f1555,plain,
    ( ~ spl6_27
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f1554,f511,f507,f280,f275,f270,f167,f163,f159,f155,f151,f559])).

fof(f1554,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1553,f282])).

fof(f1553,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1552,f272])).

fof(f1552,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1551,f277])).

fof(f1551,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1550,f508])).

fof(f1550,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1549,f512])).

fof(f1549,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1548,f152])).

fof(f1548,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1547,f156])).

fof(f1547,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1546,f160])).

fof(f1546,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1505,f168])).

fof(f168,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f1505,plain,
    ( ~ r2_hidden(sK3(k7_lattice3(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_8 ),
    inference(resolution,[],[f165,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1535,plain,
    ( spl6_25
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f1534,f511,f507,f280,f275,f270,f167,f163,f159,f155,f151,f537])).

fof(f1534,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1533,f282])).

fof(f1533,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1532,f272])).

fof(f1532,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1531,f277])).

fof(f1531,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1530,f508])).

fof(f1530,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1529,f512])).

fof(f1529,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1528,f152])).

fof(f1528,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1527,f156])).

fof(f1527,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1526,f160])).

fof(f1526,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1503,f168])).

fof(f1503,plain,
    ( r2_hidden(k13_lattice3(k7_lattice3(sK0),sK2(k7_lattice3(sK0),sK1),sK3(k7_lattice3(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_8 ),
    inference(resolution,[],[f165,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | r2_hidden(k13_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1525,plain,
    ( spl6_24
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f1524,f511,f507,f280,f275,f270,f167,f163,f159,f155,f151,f526])).

fof(f1524,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1523,f282])).

fof(f1523,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1522,f272])).

fof(f1522,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1521,f277])).

fof(f1521,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1520,f508])).

fof(f1520,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1519,f512])).

fof(f1519,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1518,f152])).

fof(f1518,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1517,f156])).

fof(f1517,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1516,f160])).

fof(f1516,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1502,f168])).

fof(f1502,plain,
    ( m1_subset_1(sK3(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_8 ),
    inference(resolution,[],[f165,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1515,plain,
    ( spl6_23
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f1514,f511,f507,f280,f275,f270,f167,f163,f159,f155,f151,f515])).

fof(f1514,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1513,f282])).

fof(f1513,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1512,f272])).

fof(f1512,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1511,f277])).

fof(f1511,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_21
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1510,f508])).

fof(f1510,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1509,f512])).

fof(f1509,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1508,f152])).

fof(f1508,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1507,f156])).

fof(f1507,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | ~ spl6_7
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1506,f160])).

fof(f1506,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f1501,f168])).

fof(f1501,plain,
    ( m1_subset_1(sK2(k7_lattice3(sK0),sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ v1_lattice3(k7_lattice3(sK0))
    | ~ v5_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(k7_lattice3(sK0))
    | spl6_8 ),
    inference(resolution,[],[f165,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1499,plain,
    ( spl6_3
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_85 ),
    inference(avatar_split_clause,[],[f1498,f1248,f222,f217,f212,f202,f197,f151,f147,f139,f135,f143])).

fof(f1248,plain,
    ( spl6_85
  <=> r2_hidden(k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f1498,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | spl6_85 ),
    inference(subsumption_resolution,[],[f1497,f224])).

fof(f1497,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | spl6_85 ),
    inference(subsumption_resolution,[],[f1496,f219])).

fof(f1496,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | spl6_85 ),
    inference(subsumption_resolution,[],[f1495,f214])).

fof(f1495,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | spl6_85 ),
    inference(subsumption_resolution,[],[f1494,f204])).

fof(f1494,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | spl6_85 ),
    inference(subsumption_resolution,[],[f1493,f199])).

fof(f1493,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_5
    | spl6_85 ),
    inference(subsumption_resolution,[],[f1492,f152])).

fof(f1492,plain,
    ( v1_waybel_7(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_85 ),
    inference(subsumption_resolution,[],[f1491,f136])).

fof(f1491,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_2
    | ~ spl6_4
    | spl6_85 ),
    inference(subsumption_resolution,[],[f1490,f140])).

fof(f1490,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_4
    | spl6_85 ),
    inference(subsumption_resolution,[],[f1470,f148])).

fof(f1470,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_85 ),
    inference(resolution,[],[f1250,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | r2_hidden(k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1250,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | spl6_85 ),
    inference(avatar_component_clause,[],[f1248])).

fof(f1286,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_79 ),
    inference(avatar_contradiction_clause,[],[f1285])).

fof(f1285,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1284,f224])).

fof(f1284,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1283,f219])).

fof(f1283,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1282,f214])).

fof(f1282,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1281,f204])).

fof(f1281,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1280,f199])).

fof(f1280,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1279,f152])).

fof(f1279,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1278,f136])).

fof(f1278,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1277,f140])).

fof(f1277,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1276,f148])).

fof(f1276,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_3
    | ~ spl6_79 ),
    inference(subsumption_resolution,[],[f1275,f145])).

fof(f145,plain,
    ( ~ v1_waybel_7(sK1,sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f1275,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_79 ),
    inference(resolution,[],[f1199,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1199,plain,
    ( r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f1197])).

fof(f1197,plain,
    ( spl6_79
  <=> r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f1251,plain,
    ( spl6_79
    | spl6_72
    | ~ spl6_85
    | ~ spl6_28
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f1246,f993,f840,f830,f647,f1248,f1123,f1197])).

fof(f1123,plain,
    ( spl6_72
  <=> r2_hidden(sK4(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f647,plain,
    ( spl6_28
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f830,plain,
    ( spl6_40
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f840,plain,
    ( spl6_41
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f993,plain,
    ( spl6_58
  <=> k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),sK4(sK0,sK1),sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f1246,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | r2_hidden(sK4(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl6_28
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f1245,f842])).

fof(f842,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f840])).

fof(f1245,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | r2_hidden(sK4(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl6_28
    | ~ spl6_40
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f1231,f832])).

fof(f832,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f830])).

fof(f1231,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | r2_hidden(sK4(sK0,sK1),sK1)
    | r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl6_28
    | ~ spl6_58 ),
    inference(superposition,[],[f648,f995])).

fof(f995,plain,
    ( k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),sK4(sK0,sK1),sK5(sK0,sK1))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f993])).

fof(f648,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | r2_hidden(X1,sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f647])).

fof(f1228,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_72 ),
    inference(avatar_contradiction_clause,[],[f1227])).

fof(f1227,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1226,f224])).

fof(f1226,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1225,f219])).

fof(f1225,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1224,f214])).

fof(f1224,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1223,f204])).

fof(f1223,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1222,f199])).

fof(f1222,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1221,f152])).

fof(f1221,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1220,f136])).

fof(f1220,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1219,f140])).

fof(f1219,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_3
    | ~ spl6_4
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1218,f148])).

fof(f1218,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_3
    | ~ spl6_72 ),
    inference(subsumption_resolution,[],[f1217,f145])).

fof(f1217,plain,
    ( v1_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_72 ),
    inference(resolution,[],[f1125,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1125,plain,
    ( r2_hidden(sK4(sK0,sK1),sK1)
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f1123])).

fof(f1021,plain,
    ( spl6_58
    | ~ spl6_19
    | ~ spl6_34
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f1020,f1007,f727,f381,f993])).

fof(f381,plain,
    ( spl6_19
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f727,plain,
    ( spl6_34
  <=> sK4(sK0,sK1) = k8_lattice3(sK0,sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f1007,plain,
    ( spl6_60
  <=> ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),sK5(sK0,sK1))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f1020,plain,
    ( k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),sK4(sK0,sK1),sK5(sK0,sK1))
    | ~ spl6_19
    | ~ spl6_34
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f1013,f729])).

fof(f729,plain,
    ( sK4(sK0,sK1) = k8_lattice3(sK0,sK4(sK0,sK1))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f727])).

fof(f1013,plain,
    ( k12_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,sK4(sK0,sK1)),sK5(sK0,sK1))
    | ~ spl6_19
    | ~ spl6_60 ),
    inference(resolution,[],[f1008,f383])).

fof(f383,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f381])).

fof(f1008,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),sK5(sK0,sK1)) )
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1009,plain,
    ( spl6_60
    | ~ spl6_35
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f1005,f774,f760,f1007])).

fof(f760,plain,
    ( spl6_35
  <=> ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),k8_lattice3(sK0,sK5(sK0,sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f774,plain,
    ( spl6_37
  <=> sK5(sK0,sK1) = k8_lattice3(sK0,sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f1005,plain,
    ( ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),sK5(sK0,sK1))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl6_35
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f761,f776])).

fof(f776,plain,
    ( sK5(sK0,sK1) = k8_lattice3(sK0,sK5(sK0,sK1))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f774])).

fof(f761,plain,
    ( ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),k8_lattice3(sK0,sK5(sK0,sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f760])).

fof(f843,plain,
    ( spl6_41
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f838,f774,f393,f197,f840])).

fof(f393,plain,
    ( spl6_20
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f838,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f837,f199])).

fof(f837,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl6_20
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f834,f395])).

fof(f395,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f393])).

fof(f834,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_37 ),
    inference(superposition,[],[f130,f776])).

fof(f130,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_lattice3)).

fof(f833,plain,
    ( spl6_40
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f828,f727,f381,f197,f830])).

fof(f828,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ spl6_10
    | ~ spl6_19
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f827,f199])).

fof(f827,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl6_19
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f824,f383])).

fof(f824,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl6_34 ),
    inference(superposition,[],[f130,f729])).

fof(f777,plain,
    ( spl6_37
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f772,f393,f197,f774])).

fof(f772,plain,
    ( sK5(sK0,sK1) = k8_lattice3(sK0,sK5(sK0,sK1))
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f753,f199])).

fof(f753,plain,
    ( sK5(sK0,sK1) = k8_lattice3(sK0,sK5(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ spl6_20 ),
    inference(resolution,[],[f395,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k8_lattice3(X0,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattice3)).

fof(f762,plain,
    ( spl6_35
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f758,f393,f222,f217,f212,f202,f197,f760])).

fof(f758,plain,
    ( ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),k8_lattice3(sK0,sK5(sK0,sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f757,f224])).

fof(f757,plain,
    ( ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),k8_lattice3(sK0,sK5(sK0,sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ v3_orders_2(sK0) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f756,f219])).

fof(f756,plain,
    ( ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),k8_lattice3(sK0,sK5(sK0,sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f755,f214])).

fof(f755,plain,
    ( ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),k8_lattice3(sK0,sK5(sK0,sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f754,f204])).

fof(f754,plain,
    ( ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),k8_lattice3(sK0,sK5(sK0,sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f750,f199])).

fof(f750,plain,
    ( ! [X6] :
        ( k12_lattice3(sK0,X6,sK5(sK0,sK1)) = k13_lattice3(k7_lattice3(sK0),k8_lattice3(sK0,X6),k8_lattice3(sK0,sK5(sK0,sK1)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl6_20 ),
    inference(resolution,[],[f395,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X0,X1,X2) = k13_lattice3(k7_lattice3(X0),k8_lattice3(X0,X1),k8_lattice3(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k13_lattice3(k7_lattice3(X0),k8_lattice3(X0,X1),k8_lattice3(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k12_lattice3(X0,X1,X2) = k13_lattice3(k7_lattice3(X0),k8_lattice3(X0,X1),k8_lattice3(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,X2) = k13_lattice3(k7_lattice3(X0),k8_lattice3(X0,X1),k8_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_yellow_7)).

fof(f730,plain,
    ( spl6_34
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f725,f381,f197,f727])).

fof(f725,plain,
    ( sK4(sK0,sK1) = k8_lattice3(sK0,sK4(sK0,sK1))
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f706,f199])).

fof(f706,plain,
    ( sK4(sK0,sK1) = k8_lattice3(sK0,sK4(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ spl6_19 ),
    inference(resolution,[],[f383,f131])).

fof(f649,plain,
    ( ~ spl6_22
    | spl6_28
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f645,f507,f280,f275,f270,f167,f163,f159,f155,f151,f647,f511])).

fof(f645,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ l1_orders_2(k7_lattice3(sK0)) )
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f644,f282])).

fof(f644,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f643,f272])).

fof(f643,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f642,f277])).

fof(f642,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f641,f508])).

fof(f641,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f640,f152])).

fof(f640,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f639,f156])).

fof(f639,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f638,f160])).

fof(f638,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
        | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f637,f168])).

fof(f637,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(k13_lattice3(k7_lattice3(sK0),X1,X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(k7_lattice3(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
        | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
        | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
        | v1_xboole_0(sK1)
        | ~ l1_orders_2(k7_lattice3(sK0))
        | ~ v1_lattice3(k7_lattice3(sK0))
        | ~ v5_orders_2(k7_lattice3(sK0))
        | ~ v4_orders_2(k7_lattice3(sK0))
        | ~ v3_orders_2(k7_lattice3(sK0)) )
    | ~ spl6_8 ),
    inference(resolution,[],[f164,f101])).

fof(f101,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f164,plain,
    ( v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f636,plain,
    ( spl6_20
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f635,f222,f217,f212,f202,f197,f151,f147,f143,f139,f135,f393])).

fof(f635,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f634,f224])).

fof(f634,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f633,f219])).

fof(f633,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f632,f214])).

fof(f632,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f631,f204])).

fof(f631,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f630,f199])).

fof(f630,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f629,f152])).

fof(f629,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f628,f136])).

fof(f628,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f627,f140])).

fof(f627,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f613,f148])).

fof(f613,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_3 ),
    inference(resolution,[],[f145,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f626,plain,
    ( spl6_19
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f625,f222,f217,f212,f202,f197,f151,f147,f143,f139,f135,f381])).

fof(f625,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f624,f224])).

fof(f624,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f623,f219])).

fof(f623,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f622,f214])).

fof(f622,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f621,f204])).

fof(f621,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f620,f199])).

fof(f620,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f619,f152])).

fof(f619,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f618,f136])).

fof(f618,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | ~ spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f617,f140])).

fof(f617,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f612,f148])).

fof(f612,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | spl6_3 ),
    inference(resolution,[],[f145,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( v1_waybel_7(X1,X0)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f611,plain,
    ( ~ spl6_10
    | spl6_22 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl6_10
    | spl6_22 ),
    inference(subsumption_resolution,[],[f609,f199])).

fof(f609,plain,
    ( ~ l1_orders_2(sK0)
    | spl6_22 ),
    inference(resolution,[],[f513,f127])).

fof(f127,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattice3)).

fof(f513,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f511])).

fof(f566,plain,
    ( ~ spl6_10
    | ~ spl6_11
    | spl6_21 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_11
    | spl6_21 ),
    inference(subsumption_resolution,[],[f564,f204])).

fof(f564,plain,
    ( ~ v2_lattice3(sK0)
    | ~ spl6_10
    | spl6_21 ),
    inference(subsumption_resolution,[],[f563,f199])).

fof(f563,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | spl6_21 ),
    inference(resolution,[],[f509,f121])).

fof(f121,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_lattice3(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => v1_lattice3(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0) )
     => ( v1_lattice3(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_7)).

fof(f509,plain,
    ( ~ v1_lattice3(k7_lattice3(sK0))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f507])).

fof(f484,plain,
    ( ~ spl6_4
    | ~ spl6_2
    | spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f483,f197,f159,f139,f147])).

fof(f483,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | spl6_7
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f482,f199])).

fof(f482,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl6_2
    | spl6_7 ),
    inference(subsumption_resolution,[],[f481,f140])).

fof(f481,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v12_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | spl6_7 ),
    inference(resolution,[],[f161,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v13_waybel_0(X1,k7_lattice3(X0)) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v13_waybel_0(X1,k7_lattice3(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v12_waybel_0(X1,X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v13_waybel_0(X1,k7_lattice3(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow_7)).

fof(f161,plain,
    ( ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f465,plain,
    ( ~ spl6_9
    | spl6_4
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f464,f197,f155,f147,f167])).

fof(f464,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f457,f199])).

fof(f457,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ l1_orders_2(sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f156,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f455,plain,
    ( ~ spl6_4
    | ~ spl6_1
    | spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f454,f197,f155,f135,f147])).

fof(f454,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_1
    | spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f453,f199])).

fof(f453,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl6_1
    | spl6_6 ),
    inference(subsumption_resolution,[],[f452,f136])).

fof(f452,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | spl6_6 ),
    inference(resolution,[],[f157,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,k7_lattice3(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f157,plain,
    ( ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f155])).

fof(f427,plain,
    ( ~ spl6_9
    | spl6_2
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f426,f197,f159,f139,f167])).

fof(f426,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f413,f199])).

fof(f413,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ l1_orders_2(sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f160,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v13_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f359,plain,
    ( ~ spl6_9
    | spl6_1
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f358,f197,f155,f135,f167])).

fof(f358,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f345,f199])).

fof(f345,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ l1_orders_2(sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f156,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
      | ~ v2_waybel_0(X1,k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f283,plain,
    ( ~ spl6_15
    | spl6_18
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f263,f197,f280,f222])).

fof(f263,plain,
    ( v3_orders_2(k7_lattice3(sK0))
    | ~ v3_orders_2(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f199,f126])).

fof(f126,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v3_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v3_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v3_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_yellow_7)).

fof(f278,plain,
    ( ~ spl6_13
    | spl6_17
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f262,f197,f275,f212])).

fof(f262,plain,
    ( v5_orders_2(k7_lattice3(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f199,f125])).

fof(f125,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v5_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => v5_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v5_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_yellow_7)).

fof(f273,plain,
    ( ~ spl6_14
    | spl6_16
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f261,f197,f270,f217])).

fof(f261,plain,
    ( v4_orders_2(k7_lattice3(sK0))
    | ~ v4_orders_2(sK0)
    | ~ spl6_10 ),
    inference(resolution,[],[f199,f124])).

fof(f124,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v4_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => v4_orders_2(k7_lattice3(X0)) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ( v4_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_yellow_7)).

fof(f225,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f69,f222])).

fof(f69,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
      | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
      | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
      | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_waybel_7(sK1,sK0)
      | ~ v12_waybel_0(sK1,sK0)
      | ~ v1_waybel_0(sK1,sK0)
      | v1_xboole_0(sK1) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
        & v2_waybel_7(sK1,k7_lattice3(sK0))
        & v13_waybel_0(sK1,k7_lattice3(sK0))
        & v2_waybel_0(sK1,k7_lattice3(sK0))
        & ~ v1_xboole_0(sK1) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v1_waybel_7(sK1,sK0)
        & v12_waybel_0(sK1,sK0)
        & v1_waybel_0(sK1,sK0)
        & ~ v1_xboole_0(sK1) ) )
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f51,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              | ~ v2_waybel_7(X1,k7_lattice3(X0))
              | ~ v13_waybel_0(X1,k7_lattice3(X0))
              | ~ v2_waybel_0(X1,k7_lattice3(X0))
              | v1_xboole_0(X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_waybel_7(X1,X0)
              | ~ v12_waybel_0(X1,X0)
              | ~ v1_waybel_0(X1,X0)
              | v1_xboole_0(X1) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
                & v2_waybel_7(X1,k7_lattice3(X0))
                & v13_waybel_0(X1,k7_lattice3(X0))
                & v2_waybel_0(X1,k7_lattice3(X0))
                & ~ v1_xboole_0(X1) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_waybel_7(X1,X0)
                & v12_waybel_0(X1,X0)
                & v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) ) ) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
            | ~ v2_waybel_7(X1,k7_lattice3(sK0))
            | ~ v13_waybel_0(X1,k7_lattice3(sK0))
            | ~ v2_waybel_0(X1,k7_lattice3(sK0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v1_waybel_7(X1,sK0)
            | ~ v12_waybel_0(X1,sK0)
            | ~ v1_waybel_0(X1,sK0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
              & v2_waybel_7(X1,k7_lattice3(sK0))
              & v13_waybel_0(X1,k7_lattice3(sK0))
              & v2_waybel_0(X1,k7_lattice3(sK0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v1_waybel_7(X1,sK0)
              & v12_waybel_0(X1,sK0)
              & v1_waybel_0(X1,sK0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
          | ~ v2_waybel_7(X1,k7_lattice3(sK0))
          | ~ v13_waybel_0(X1,k7_lattice3(sK0))
          | ~ v2_waybel_0(X1,k7_lattice3(sK0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v1_waybel_7(X1,sK0)
          | ~ v12_waybel_0(X1,sK0)
          | ~ v1_waybel_0(X1,sK0)
          | v1_xboole_0(X1) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
            & v2_waybel_7(X1,k7_lattice3(sK0))
            & v13_waybel_0(X1,k7_lattice3(sK0))
            & v2_waybel_0(X1,k7_lattice3(sK0))
            & ~ v1_xboole_0(X1) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v1_waybel_7(X1,sK0)
            & v12_waybel_0(X1,sK0)
            & v1_waybel_0(X1,sK0)
            & ~ v1_xboole_0(X1) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
        | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
        | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
        | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_waybel_7(sK1,sK0)
        | ~ v12_waybel_0(sK1,sK0)
        | ~ v1_waybel_0(sK1,sK0)
        | v1_xboole_0(sK1) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
          & v2_waybel_7(sK1,k7_lattice3(sK0))
          & v13_waybel_0(sK1,k7_lattice3(sK0))
          & v2_waybel_0(sK1,k7_lattice3(sK0))
          & ~ v1_xboole_0(sK1) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v1_waybel_7(sK1,sK0)
          & v12_waybel_0(sK1,sK0)
          & v1_waybel_0(sK1,sK0)
          & ~ v1_xboole_0(sK1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            | ~ v2_waybel_7(X1,k7_lattice3(X0))
            | ~ v13_waybel_0(X1,k7_lattice3(X0))
            | ~ v2_waybel_0(X1,k7_lattice3(X0))
            | v1_xboole_0(X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_waybel_7(X1,X0)
            | ~ v12_waybel_0(X1,X0)
            | ~ v1_waybel_0(X1,X0)
            | v1_xboole_0(X1) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) ) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_waybel_7(X1,X0)
              & v12_waybel_0(X1,X0)
              & v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
              & v2_waybel_7(X1,k7_lattice3(X0))
              & v13_waybel_0(X1,k7_lattice3(X0))
              & v2_waybel_0(X1,k7_lattice3(X0))
              & ~ v1_xboole_0(X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_waybel_7(X1,X0)
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k7_lattice3(X0))))
            & v2_waybel_7(X1,k7_lattice3(X0))
            & v13_waybel_0(X1,k7_lattice3(X0))
            & v2_waybel_0(X1,k7_lattice3(X0))
            & ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_7)).

fof(f220,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f70,f217])).

fof(f70,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f215,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f71,f212])).

fof(f71,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f205,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f73,f202])).

fof(f73,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f200,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f74,f197])).

fof(f74,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f195,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f132,f151])).

fof(f132,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f189,plain,
    ( spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f81,f155,f135])).

fof(f81,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f186,plain,
    ( spl6_4
    | spl6_6 ),
    inference(avatar_split_clause,[],[f84,f155,f147])).

fof(f84,plain,
    ( v2_waybel_0(sK1,k7_lattice3(sK0))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f183,plain,
    ( spl6_2
    | spl6_7 ),
    inference(avatar_split_clause,[],[f87,f159,f139])).

fof(f87,plain,
    ( v13_waybel_0(sK1,k7_lattice3(sK0))
    | v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f177,plain,
    ( spl6_3
    | spl6_8 ),
    inference(avatar_split_clause,[],[f93,f163,f143])).

fof(f93,plain,
    ( v2_waybel_7(sK1,k7_lattice3(sK0))
    | v1_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f174,plain,
    ( spl6_1
    | spl6_9 ),
    inference(avatar_split_clause,[],[f96,f167,f135])).

fof(f96,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f171,plain,
    ( spl6_4
    | spl6_9 ),
    inference(avatar_split_clause,[],[f99,f167,f147])).

fof(f99,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f54])).

fof(f170,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f133,f167,f163,f159,f155,f151,f147,f143,f139,f135])).

fof(f133,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k7_lattice3(sK0))))
    | ~ v2_waybel_7(sK1,k7_lattice3(sK0))
    | ~ v13_waybel_0(sK1,k7_lattice3(sK0))
    | ~ v2_waybel_0(sK1,k7_lattice3(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_waybel_7(sK1,sK0)
    | ~ v12_waybel_0(sK1,sK0)
    | ~ v1_waybel_0(sK1,sK0)
    | v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

%------------------------------------------------------------------------------
