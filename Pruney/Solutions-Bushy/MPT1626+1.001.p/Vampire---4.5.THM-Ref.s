%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1626+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 259 expanded)
%              Number of leaves         :   10 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  379 (3244 expanded)
%              Number of equality atoms :   41 ( 546 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f118,f127])).

fof(f127,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f19,f24,f26,f41,f23,f25,f28,f27,f69,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_yellow_0(X2,X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_yellow_0(X2,X0)
      | sQ4_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X2,X1))
      | v2_struct_0(X2)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sQ4_eqProxy(k1_xboole_0,X1)
      | ~ v2_waybel_0(X1,X2)
      | ~ v3_waybel_0(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_yellow_0(X0,X1),k2_yellow_0(X2,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_yellow_0(X2,X0)
      | ~ v4_yellow_0(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | sQ4_eqProxy(k1_xboole_0,X1)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v2_waybel_0(X1,X2)
      | ~ v3_waybel_0(X2,X0)
      | ~ m1_yellow_0(X2,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k2_yellow_0(X0,X3),u1_struct_0(X1))
      | sQ4_eqProxy(k1_xboole_0,X3)
      | ~ r2_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_waybel_0(X3,X1)
      | ~ v3_waybel_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f33,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k2_yellow_0(X0,X3),u1_struct_0(X1))
      | k1_xboole_0 = X3
      | ~ r2_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_waybel_0(X3,X1)
      | ~ v3_waybel_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_waybel_0(X1,X0)
              | ( ~ r2_hidden(k2_yellow_0(X0,sK3(X0,X1)),u1_struct_0(X1))
                & k1_xboole_0 != sK3(X0,X1)
                & r2_yellow_0(X0,sK3(X0,X1))
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_0(sK3(X0,X1),X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r2_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v2_waybel_0(X3,X1) )
              | ~ v3_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
          & k1_xboole_0 != X2
          & r2_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v2_waybel_0(X2,X1) )
     => ( ~ r2_hidden(k2_yellow_0(X0,sK3(X0,X1)),u1_struct_0(X1))
        & k1_xboole_0 != sK3(X0,X1)
        & r2_yellow_0(X0,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
        & v2_waybel_0(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r2_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r2_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v2_waybel_0(X3,X1) )
              | ~ v3_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r2_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) ) )
            & ( ! [X2] :
                  ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  | k1_xboole_0 = X2
                  | ~ r2_yellow_0(X0,X2)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v2_waybel_0(X2,X1) )
              | ~ v3_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r2_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r2_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v3_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) )
               => ( r2_yellow_0(X0,X2)
                 => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                    | k1_xboole_0 = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_0)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | sQ4_eqProxy(k2_yellow_0(X0,X2),k2_yellow_0(X1,X2))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f32,f39])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
      | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_yellow_0)).

fof(f69,plain,
    ( ~ sQ4_eqProxy(k2_yellow_0(sK0,sK2),k2_yellow_0(sK1,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_2
  <=> sQ4_eqProxy(k2_yellow_0(sK0,sK2),k2_yellow_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
      | ~ r2_yellow_0(sK1,sK2) )
    & k1_xboole_0 != sK2
    & r2_yellow_0(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & v2_waybel_0(sK2,sK1)
    & m1_yellow_0(sK1,sK0)
    & v3_waybel_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                  | ~ r2_yellow_0(X1,X2) )
                & k1_xboole_0 != X2
                & r2_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_0(X2,X1) )
            & m1_yellow_0(X1,X0)
            & v3_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X1,X2) != k2_yellow_0(sK0,X2)
                | ~ r2_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r2_yellow_0(sK0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v2_waybel_0(X2,X1) )
          & m1_yellow_0(X1,sK0)
          & v3_waybel_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_yellow_0(X1,X2) != k2_yellow_0(sK0,X2)
              | ~ r2_yellow_0(X1,X2) )
            & k1_xboole_0 != X2
            & r2_yellow_0(sK0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            & v2_waybel_0(X2,X1) )
        & m1_yellow_0(X1,sK0)
        & v3_waybel_0(X1,sK0)
        & v4_yellow_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_yellow_0(sK0,X2) != k2_yellow_0(sK1,X2)
            | ~ r2_yellow_0(sK1,X2) )
          & k1_xboole_0 != X2
          & r2_yellow_0(sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
          & v2_waybel_0(X2,sK1) )
      & m1_yellow_0(sK1,sK0)
      & v3_waybel_0(sK1,sK0)
      & v4_yellow_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ( k2_yellow_0(sK0,X2) != k2_yellow_0(sK1,X2)
          | ~ r2_yellow_0(sK1,X2) )
        & k1_xboole_0 != X2
        & r2_yellow_0(sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        & v2_waybel_0(X2,sK1) )
   => ( ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
        | ~ r2_yellow_0(sK1,sK2) )
      & k1_xboole_0 != sK2
      & r2_yellow_0(sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
      & v2_waybel_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v2_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v3_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v2_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v3_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v3_waybel_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) )
               => ( r2_yellow_0(X0,X2)
                 => ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                      & r2_yellow_0(X1,X2) )
                    | k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v3_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_0(X2,X1) )
             => ( r2_yellow_0(X0,X2)
               => ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                    & r2_yellow_0(X1,X2) )
                  | k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_waybel_0)).

fof(f28,plain,(
    r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,sK2) ),
    inference(equality_proxy_replacement,[],[f29,f39])).

fof(f29,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    v2_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    v3_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f118,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f19,f24,f25,f23,f28,f26,f41,f65,f27,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_yellow_0(X0,X2)
      | ~ r2_yellow_0(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_yellow_0(X0,X2)
      | r2_yellow_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | sQ4_eqProxy(k1_xboole_0,X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v3_waybel_0(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X0,X1)
      | ~ r2_yellow_0(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_yellow_0(X0,X2)
      | ~ v4_yellow_0(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | sQ4_eqProxy(k1_xboole_0,X1)
      | ~ r2_yellow_0(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ v3_waybel_0(X0,X2)
      | ~ m1_yellow_0(X0,X2)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f31,f44])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | r2_yellow_0(X1,X2)
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,
    ( ~ r2_yellow_0(sK1,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_1
  <=> r2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f70,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f40,f67,f63])).

fof(f40,plain,
    ( ~ sQ4_eqProxy(k2_yellow_0(sK0,sK2),k2_yellow_0(sK1,sK2))
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f30,f39])).

fof(f30,plain,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
