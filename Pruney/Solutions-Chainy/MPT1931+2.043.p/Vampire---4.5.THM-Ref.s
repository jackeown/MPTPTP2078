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
% DateTime   : Thu Dec  3 13:22:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 121 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :  279 ( 565 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f88,f93,f98,f103,f170,f186])).

fof(f186,plain,
    ( spl5_1
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_17 ),
    inference(avatar_split_clause,[],[f185,f167,f95,f90,f85,f70,f65])).

fof(f65,plain,
    ( spl5_1
  <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f70,plain,
    ( spl5_2
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f85,plain,
    ( spl5_5
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f90,plain,
    ( spl5_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f95,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f167,plain,
    ( spl5_17
  <=> r2_waybel_0(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f185,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_17 ),
    inference(forward_demodulation,[],[f171,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f171,plain,
    ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_7
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f97,f92,f87,f72,f169,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f57,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f169,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f72,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f87,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f92,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f97,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f170,plain,
    ( ~ spl5_17
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f165,f100,f95,f90,f85,f70,f167])).

fof(f100,plain,
    ( spl5_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f165,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f97,f92,f87,f72,f56,f110,f51])).

fof(f51,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
                      & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f32,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f110,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f102,f45,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f102,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f103,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f44,f100])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f98,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f37,f95])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f93,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f39,f85])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f70])).

fof(f42,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f43,f65])).

fof(f43,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:48:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (10207)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.42  % (10207)Refutation not found, incomplete strategy% (10207)------------------------------
% 0.22/0.42  % (10207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (10207)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.42  
% 0.22/0.42  % (10207)Memory used [KB]: 10618
% 0.22/0.42  % (10207)Time elapsed: 0.004 s
% 0.22/0.42  % (10207)------------------------------
% 0.22/0.42  % (10207)------------------------------
% 0.22/0.46  % (10202)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.46  % (10196)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (10202)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f187,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f68,f73,f88,f93,f98,f103,f170,f186])).
% 0.22/0.46  fof(f186,plain,(
% 0.22/0.46    spl5_1 | ~spl5_2 | spl5_5 | ~spl5_6 | spl5_7 | spl5_17),
% 0.22/0.46    inference(avatar_split_clause,[],[f185,f167,f95,f90,f85,f70,f65])).
% 0.22/0.46  fof(f65,plain,(
% 0.22/0.46    spl5_1 <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.46  fof(f70,plain,(
% 0.22/0.46    spl5_2 <=> l1_waybel_0(sK1,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.46  fof(f85,plain,(
% 0.22/0.46    spl5_5 <=> v2_struct_0(sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.46  fof(f90,plain,(
% 0.22/0.46    spl5_6 <=> l1_struct_0(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    spl5_7 <=> v2_struct_0(sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.46  fof(f167,plain,(
% 0.22/0.46    spl5_17 <=> r2_waybel_0(sK0,sK1,k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.46  fof(f185,plain,(
% 0.22/0.46    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | (~spl5_2 | spl5_5 | ~spl5_6 | spl5_7 | spl5_17)),
% 0.22/0.46    inference(forward_demodulation,[],[f171,f46])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.46  fof(f171,plain,(
% 0.22/0.46    r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | (~spl5_2 | spl5_5 | ~spl5_6 | spl5_7 | spl5_17)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f97,f92,f87,f72,f169,f62])).
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f48,f57])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.46  fof(f48,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f28])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(nnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.22/0.46  fof(f169,plain,(
% 0.22/0.46    ~r2_waybel_0(sK0,sK1,k1_xboole_0) | spl5_17),
% 0.22/0.46    inference(avatar_component_clause,[],[f167])).
% 0.22/0.46  fof(f72,plain,(
% 0.22/0.46    l1_waybel_0(sK1,sK0) | ~spl5_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f70])).
% 0.22/0.46  fof(f87,plain,(
% 0.22/0.46    ~v2_struct_0(sK1) | spl5_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f85])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    l1_struct_0(sK0) | ~spl5_6),
% 0.22/0.46    inference(avatar_component_clause,[],[f90])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    ~v2_struct_0(sK0) | spl5_7),
% 0.22/0.46    inference(avatar_component_clause,[],[f95])).
% 0.22/0.46  fof(f170,plain,(
% 0.22/0.46    ~spl5_17 | ~spl5_2 | spl5_5 | ~spl5_6 | spl5_7 | ~spl5_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f165,f100,f95,f90,f85,f70,f167])).
% 0.22/0.46  fof(f100,plain,(
% 0.22/0.46    spl5_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.46  fof(f165,plain,(
% 0.22/0.46    ~r2_waybel_0(sK0,sK1,k1_xboole_0) | (~spl5_2 | spl5_5 | ~spl5_6 | spl5_7 | ~spl5_8)),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f97,f92,f87,f72,f56,f110,f51])).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    ( ! [X2,X0,X5,X1] : (~r2_waybel_0(X0,X1,X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f32,f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(rectify,[],[f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(nnf_transformation,[],[f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.22/0.46  fof(f110,plain,(
% 0.22/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_8),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f102,f45,f61])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0) | ~spl5_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f100])).
% 0.22/0.46  fof(f56,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f35])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.46  fof(f103,plain,(
% 0.22/0.46    spl5_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f44,f100])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.46  fof(f98,plain,(
% 0.22/0.46    ~spl5_7),
% 0.22/0.46    inference(avatar_split_clause,[],[f37,f95])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ~v2_struct_0(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f26,f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.46    inference(flattening,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,negated_conjecture,(
% 0.22/0.46    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.46    inference(negated_conjecture,[],[f12])).
% 0.22/0.46  fof(f12,conjecture,(
% 0.22/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    spl5_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f38,f90])).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    l1_struct_0(sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    ~spl5_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f39,f85])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ~v2_struct_0(sK1)),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  fof(f73,plain,(
% 0.22/0.46    spl5_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f42,f70])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    l1_waybel_0(sK1,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    ~spl5_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f43,f65])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.22/0.46    inference(cnf_transformation,[],[f27])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (10202)------------------------------
% 0.22/0.46  % (10202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (10202)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (10202)Memory used [KB]: 6140
% 0.22/0.46  % (10202)Time elapsed: 0.032 s
% 0.22/0.46  % (10202)------------------------------
% 0.22/0.46  % (10202)------------------------------
% 0.22/0.46  % (10195)Success in time 0.097 s
%------------------------------------------------------------------------------
