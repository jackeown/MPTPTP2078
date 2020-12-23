%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 573 expanded)
%              Number of leaves         :   28 ( 266 expanded)
%              Depth                    :   10
%              Number of atoms          :  668 (4840 expanded)
%              Number of equality atoms :   66 ( 671 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f894,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f247,f251,f340,f405,f409,f413,f422,f506,f530,f531,f532,f537,f539,f556,f589,f643,f706,f727,f847,f889])).

fof(f889,plain,
    ( spl4_71
    | ~ spl4_22
    | ~ spl4_82
    | ~ spl4_101 ),
    inference(avatar_split_clause,[],[f880,f844,f704,f233,f640])).

fof(f640,plain,
    ( spl4_71
  <=> r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f233,plain,
    ( spl4_22
  <=> m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f704,plain,
    ( spl4_82
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f844,plain,
    ( spl4_101
  <=> r2_hidden(sK3(sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).

fof(f880,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
    | r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1))
    | ~ spl4_82
    | ~ spl4_101 ),
    inference(resolution,[],[f705,f846])).

fof(f846,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ spl4_101 ),
    inference(avatar_component_clause,[],[f844])).

fof(f705,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1)) )
    | ~ spl4_82 ),
    inference(avatar_component_clause,[],[f704])).

fof(f847,plain,
    ( spl4_101
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_86 ),
    inference(avatar_split_clause,[],[f839,f725,f238,f233,f844])).

fof(f238,plain,
    ( spl4_23
  <=> r2_hidden(sK3(sK0,sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f725,plain,
    ( spl4_86
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f839,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,sK2,sK1),sK1)
    | ~ spl4_23
    | ~ spl4_86 ),
    inference(resolution,[],[f726,f240])).

fof(f240,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f238])).

fof(f726,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) )
    | ~ spl4_86 ),
    inference(avatar_component_clause,[],[f725])).

fof(f727,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_26
    | ~ spl4_20
    | spl4_86
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f716,f271,f725,f225,f261,f76,f72,f68,f64,f135])).

fof(f135,plain,
    ( spl4_16
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f64,plain,
    ( spl4_1
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f68,plain,
    ( spl4_2
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f72,plain,
    ( spl4_3
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f76,plain,
    ( spl4_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f261,plain,
    ( spl4_26
  <=> m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f225,plain,
    ( spl4_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f271,plain,
    ( spl4_28
  <=> sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f716,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_28 ),
    inference(superposition,[],[f45,f273])).

fof(f273,plain,
    ( sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f271])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f706,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_19
    | spl4_82
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f698,f243,f704,f221,f233,f76,f72,f68,f64,f135])).

fof(f221,plain,
    ( spl4_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f243,plain,
    ( spl4_24
  <=> sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f698,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_24 ),
    inference(superposition,[],[f44,f245])).

fof(f245,plain,
    ( sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f243])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f643,plain,
    ( ~ spl4_4
    | spl4_17
    | ~ spl4_71
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f612,f233,f640,f207,f76])).

fof(f207,plain,
    ( spl4_17
  <=> ! [X18] : ~ m1_subset_1(X18,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f612,plain,
    ( ! [X12] :
        ( ~ r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_22 ),
    inference(resolution,[],[f235,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(f235,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f233])).

fof(f589,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f27,f28,f29,f30,f31,f36,f32,f223,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f223,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f221])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    & m1_orders_2(sK1,sK0,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( m1_orders_2(X2,X0,X1)
                & m1_orders_2(X1,X0,X2)
                & k1_xboole_0 != X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,sK0,X1)
              & m1_orders_2(X1,sK0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( m1_orders_2(X2,sK0,X1)
            & m1_orders_2(X1,sK0,X2)
            & k1_xboole_0 != X1
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( m1_orders_2(X2,sK0,sK1)
          & m1_orders_2(sK1,sK0,X2)
          & k1_xboole_0 != sK1
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( m1_orders_2(X2,sK0,sK1)
        & m1_orders_2(sK1,sK0,X2)
        & k1_xboole_0 != sK1
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( m1_orders_2(sK2,sK0,sK1)
      & m1_orders_2(sK1,sK0,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( m1_orders_2(X2,X0,X1)
                    & m1_orders_2(X1,X0,X2)
                    & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(f36,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f556,plain,(
    ~ spl4_17 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f27,f28,f29,f30,f31,f34,f36,f32,f208,f33,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
                        & r2_hidden(sK3(X0,X1,X2),X1)
                        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f208,plain,
    ( ! [X18] : ~ m1_subset_1(X18,u1_struct_0(sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f207])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f539,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_20
    | ~ spl4_19
    | spl4_25
    | spl4_28 ),
    inference(avatar_split_clause,[],[f535,f271,f257,f221,f225,f76,f72,f68,f64,f135])).

fof(f257,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f535,plain,
    ( sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f36,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f537,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_20
    | ~ spl4_19
    | spl4_25
    | spl4_26 ),
    inference(avatar_split_clause,[],[f533,f261,f257,f221,f225,f76,f72,f68,f64,f135])).

fof(f533,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f36,f38])).

fof(f532,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_20
    | spl4_21
    | spl4_24 ),
    inference(avatar_split_clause,[],[f528,f243,f229,f225,f221,f76,f72,f68,f64,f135])).

fof(f229,plain,
    ( spl4_21
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f528,plain,
    ( sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f40])).

fof(f35,plain,(
    m1_orders_2(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f531,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_20
    | spl4_21
    | spl4_23 ),
    inference(avatar_split_clause,[],[f527,f238,f229,f225,f221,f76,f72,f68,f64,f135])).

fof(f527,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f530,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_20
    | spl4_21
    | spl4_22 ),
    inference(avatar_split_clause,[],[f526,f233,f229,f225,f221,f76,f72,f68,f64,f135])).

fof(f526,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f38])).

fof(f506,plain,(
    ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f27,f28,f29,f30,f31,f34,f416,f32,f414,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f414,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_21 ),
    inference(backward_demodulation,[],[f33,f231])).

fof(f231,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f229])).

fof(f416,plain,
    ( m1_orders_2(sK1,sK0,k1_xboole_0)
    | ~ spl4_21 ),
    inference(backward_demodulation,[],[f35,f231])).

fof(f422,plain,(
    ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f34,f259])).

fof(f259,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f257])).

fof(f413,plain,(
    ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f27,f137])).

fof(f137,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f409,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f31,f78])).

fof(f78,plain,
    ( ~ l1_orders_2(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f405,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f30,f74])).

fof(f74,plain,
    ( ~ v5_orders_2(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f340,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f29,f70])).

fof(f70,plain,
    ( ~ v4_orders_2(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f251,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f28,f66])).

fof(f66,plain,
    ( ~ v3_orders_2(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f247,plain,
    ( spl4_16
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_19
    | spl4_20 ),
    inference(avatar_split_clause,[],[f219,f225,f221,f76,f72,f68,f64,f135])).

fof(f219,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f35,f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (29604)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.44  % (29604)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f894,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f247,f251,f340,f405,f409,f413,f422,f506,f530,f531,f532,f537,f539,f556,f589,f643,f706,f727,f847,f889])).
% 0.21/0.44  fof(f889,plain,(
% 0.21/0.44    spl4_71 | ~spl4_22 | ~spl4_82 | ~spl4_101),
% 0.21/0.44    inference(avatar_split_clause,[],[f880,f844,f704,f233,f640])).
% 0.21/0.44  fof(f640,plain,(
% 0.21/0.44    spl4_71 <=> r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 0.21/0.44  fof(f233,plain,(
% 0.21/0.44    spl4_22 <=> m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.44  fof(f704,plain,(
% 0.21/0.44    spl4_82 <=> ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 0.21/0.44  fof(f844,plain,(
% 0.21/0.44    spl4_101 <=> r2_hidden(sK3(sK0,sK2,sK1),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_101])])).
% 0.21/0.44  fof(f880,plain,(
% 0.21/0.44    ~m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1)) | (~spl4_82 | ~spl4_101)),
% 0.21/0.44    inference(resolution,[],[f705,f846])).
% 0.21/0.44  fof(f846,plain,(
% 0.21/0.44    r2_hidden(sK3(sK0,sK2,sK1),sK1) | ~spl4_101),
% 0.21/0.44    inference(avatar_component_clause,[],[f844])).
% 0.21/0.44  fof(f705,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1))) ) | ~spl4_82),
% 0.21/0.44    inference(avatar_component_clause,[],[f704])).
% 0.21/0.44  fof(f847,plain,(
% 0.21/0.44    spl4_101 | ~spl4_22 | ~spl4_23 | ~spl4_86),
% 0.21/0.44    inference(avatar_split_clause,[],[f839,f725,f238,f233,f844])).
% 0.21/0.44  fof(f238,plain,(
% 0.21/0.44    spl4_23 <=> r2_hidden(sK3(sK0,sK2,sK1),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.44  fof(f725,plain,(
% 0.21/0.44    spl4_86 <=> ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).
% 0.21/0.44  fof(f839,plain,(
% 0.21/0.44    ~m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | r2_hidden(sK3(sK0,sK2,sK1),sK1) | (~spl4_23 | ~spl4_86)),
% 0.21/0.44    inference(resolution,[],[f726,f240])).
% 0.21/0.44  fof(f240,plain,(
% 0.21/0.44    r2_hidden(sK3(sK0,sK2,sK1),sK2) | ~spl4_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f238])).
% 0.21/0.44  fof(f726,plain,(
% 0.21/0.44    ( ! [X1] : (~r2_hidden(X1,sK2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1)) ) | ~spl4_86),
% 0.21/0.44    inference(avatar_component_clause,[],[f725])).
% 0.21/0.44  fof(f727,plain,(
% 0.21/0.44    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_26 | ~spl4_20 | spl4_86 | ~spl4_28),
% 0.21/0.44    inference(avatar_split_clause,[],[f716,f271,f725,f225,f261,f76,f72,f68,f64,f135])).
% 0.21/0.44  fof(f135,plain,(
% 0.21/0.44    spl4_16 <=> v2_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl4_1 <=> v3_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    spl4_2 <=> v4_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl4_3 <=> v5_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    spl4_4 <=> l1_orders_2(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.44  fof(f261,plain,(
% 0.21/0.44    spl4_26 <=> m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.44  fof(f225,plain,(
% 0.21/0.44    spl4_20 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.44  fof(f271,plain,(
% 0.21/0.44    spl4_28 <=> sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.44  fof(f716,plain,(
% 0.21/0.44    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_28),
% 0.21/0.44    inference(superposition,[],[f45,f273])).
% 0.21/0.44  fof(f273,plain,(
% 0.21/0.44    sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | ~spl4_28),
% 0.21/0.44    inference(avatar_component_clause,[],[f271])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.44  fof(f706,plain,(
% 0.21/0.44    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_22 | ~spl4_19 | spl4_82 | ~spl4_24),
% 0.21/0.44    inference(avatar_split_clause,[],[f698,f243,f704,f221,f233,f76,f72,f68,f64,f135])).
% 0.21/0.44  fof(f221,plain,(
% 0.21/0.44    spl4_19 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.44  fof(f243,plain,(
% 0.21/0.44    spl4_24 <=> sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.44  fof(f698,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_24),
% 0.21/0.44    inference(superposition,[],[f44,f245])).
% 0.21/0.44  fof(f245,plain,(
% 0.21/0.44    sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) | ~spl4_24),
% 0.21/0.44    inference(avatar_component_clause,[],[f243])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f643,plain,(
% 0.21/0.44    ~spl4_4 | spl4_17 | ~spl4_71 | ~spl4_22),
% 0.21/0.44    inference(avatar_split_clause,[],[f612,f233,f640,f207,f76])).
% 0.21/0.44  fof(f207,plain,(
% 0.21/0.44    spl4_17 <=> ! [X18] : ~m1_subset_1(X18,u1_struct_0(sK0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.44  fof(f612,plain,(
% 0.21/0.44    ( ! [X12] : (~r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1)) | ~m1_subset_1(X12,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl4_22),
% 0.21/0.44    inference(resolution,[],[f235,f47])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.44    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => ~r2_orders_2(X0,X1,X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).
% 0.21/0.44  fof(f235,plain,(
% 0.21/0.44    m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~spl4_22),
% 0.21/0.44    inference(avatar_component_clause,[],[f233])).
% 0.21/0.44  fof(f589,plain,(
% 0.21/0.44    spl4_19),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f584])).
% 0.21/0.44  fof(f584,plain,(
% 0.21/0.44    $false | spl4_19),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f27,f28,f29,f30,f31,f36,f32,f223,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.21/0.44  fof(f223,plain,(
% 0.21/0.44    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_19),
% 0.21/0.44    inference(avatar_component_clause,[],[f221])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ((m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f19,f18,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : ((m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,negated_conjecture,(
% 0.21/0.44    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.44    inference(negated_conjecture,[],[f5])).
% 0.21/0.44  fof(f5,conjecture,(
% 0.21/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    m1_orders_2(sK2,sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    l1_orders_2(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    v5_orders_2(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    v4_orders_2(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    v3_orders_2(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ~v2_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f556,plain,(
% 0.21/0.44    ~spl4_17),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f542])).
% 0.21/0.44  fof(f542,plain,(
% 0.21/0.44    $false | ~spl4_17),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f27,f28,f29,f30,f31,f34,f36,f32,f208,f33,f38])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(rectify,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(nnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.44    inference(flattening,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f208,plain,(
% 0.21/0.44    ( ! [X18] : (~m1_subset_1(X18,u1_struct_0(sK0))) ) | ~spl4_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f207])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    k1_xboole_0 != sK1),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f539,plain,(
% 0.21/0.44    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_20 | ~spl4_19 | spl4_25 | spl4_28),
% 0.21/0.44    inference(avatar_split_clause,[],[f535,f271,f257,f221,f225,f76,f72,f68,f64,f135])).
% 0.21/0.44  fof(f257,plain,(
% 0.21/0.44    spl4_25 <=> k1_xboole_0 = sK1),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.44  fof(f535,plain,(
% 0.21/0.44    sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f36,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f537,plain,(
% 0.21/0.44    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_20 | ~spl4_19 | spl4_25 | spl4_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f533,f261,f257,f221,f225,f76,f72,f68,f64,f135])).
% 0.21/0.44  fof(f533,plain,(
% 0.21/0.44    m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f36,f38])).
% 0.21/0.44  fof(f532,plain,(
% 0.21/0.44    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_19 | ~spl4_20 | spl4_21 | spl4_24),
% 0.21/0.44    inference(avatar_split_clause,[],[f528,f243,f229,f225,f221,f76,f72,f68,f64,f135])).
% 0.21/0.44  fof(f229,plain,(
% 0.21/0.44    spl4_21 <=> k1_xboole_0 = sK2),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.44  fof(f528,plain,(
% 0.21/0.44    sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f35,f40])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    m1_orders_2(sK1,sK0,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f20])).
% 0.21/0.44  fof(f531,plain,(
% 0.21/0.44    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_19 | ~spl4_20 | spl4_21 | spl4_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f527,f238,f229,f225,f221,f76,f72,f68,f64,f135])).
% 0.21/0.44  fof(f527,plain,(
% 0.21/0.44    r2_hidden(sK3(sK0,sK2,sK1),sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f35,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f530,plain,(
% 0.21/0.44    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_19 | ~spl4_20 | spl4_21 | spl4_22),
% 0.21/0.44    inference(avatar_split_clause,[],[f526,f233,f229,f225,f221,f76,f72,f68,f64,f135])).
% 0.21/0.44  fof(f526,plain,(
% 0.21/0.44    m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK2 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f35,f38])).
% 0.21/0.44  fof(f506,plain,(
% 0.21/0.44    ~spl4_21),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f485])).
% 0.21/0.44  fof(f485,plain,(
% 0.21/0.44    $false | ~spl4_21),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f27,f28,f29,f30,f31,f34,f416,f32,f414,f50])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(equality_resolution,[],[f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f414,plain,(
% 0.21/0.44    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_21),
% 0.21/0.44    inference(backward_demodulation,[],[f33,f231])).
% 0.21/0.44  fof(f231,plain,(
% 0.21/0.44    k1_xboole_0 = sK2 | ~spl4_21),
% 0.21/0.44    inference(avatar_component_clause,[],[f229])).
% 0.21/0.44  fof(f416,plain,(
% 0.21/0.44    m1_orders_2(sK1,sK0,k1_xboole_0) | ~spl4_21),
% 0.21/0.44    inference(backward_demodulation,[],[f35,f231])).
% 0.21/0.44  fof(f422,plain,(
% 0.21/0.44    ~spl4_25),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f418])).
% 0.21/0.44  fof(f418,plain,(
% 0.21/0.44    $false | ~spl4_25),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f34,f259])).
% 0.21/0.44  fof(f259,plain,(
% 0.21/0.44    k1_xboole_0 = sK1 | ~spl4_25),
% 0.21/0.44    inference(avatar_component_clause,[],[f257])).
% 0.21/0.44  fof(f413,plain,(
% 0.21/0.44    ~spl4_16),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f410])).
% 0.21/0.44  fof(f410,plain,(
% 0.21/0.44    $false | ~spl4_16),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f27,f137])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    v2_struct_0(sK0) | ~spl4_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f135])).
% 0.21/0.44  fof(f409,plain,(
% 0.21/0.44    spl4_4),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f406])).
% 0.21/0.44  fof(f406,plain,(
% 0.21/0.44    $false | spl4_4),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f31,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ~l1_orders_2(sK0) | spl4_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f76])).
% 0.21/0.44  fof(f405,plain,(
% 0.21/0.44    spl4_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f402])).
% 0.21/0.44  fof(f402,plain,(
% 0.21/0.44    $false | spl4_3),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f30,f74])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ~v5_orders_2(sK0) | spl4_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f72])).
% 0.21/0.44  fof(f340,plain,(
% 0.21/0.44    spl4_2),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f337])).
% 0.21/0.44  fof(f337,plain,(
% 0.21/0.44    $false | spl4_2),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f29,f70])).
% 0.21/0.44  fof(f70,plain,(
% 0.21/0.44    ~v4_orders_2(sK0) | spl4_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f68])).
% 0.21/0.44  fof(f251,plain,(
% 0.21/0.44    spl4_1),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f248])).
% 0.21/0.44  fof(f248,plain,(
% 0.21/0.44    $false | spl4_1),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f28,f66])).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    ~v3_orders_2(sK0) | spl4_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f64])).
% 0.21/0.44  fof(f247,plain,(
% 0.21/0.44    spl4_16 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_19 | spl4_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f219,f225,f221,f76,f72,f68,f64,f135])).
% 0.21/0.44  fof(f219,plain,(
% 0.21/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.44    inference(resolution,[],[f35,f37])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (29604)------------------------------
% 0.21/0.44  % (29604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29604)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (29604)Memory used [KB]: 6780
% 0.21/0.44  % (29604)Time elapsed: 0.046 s
% 0.21/0.44  % (29604)------------------------------
% 0.21/0.44  % (29604)------------------------------
% 0.21/0.44  % (29593)Success in time 0.088 s
%------------------------------------------------------------------------------
