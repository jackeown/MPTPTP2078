%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 166 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :   10
%              Number of atoms          :  352 ( 770 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f99,f113,f133])).

fof(f133,plain,
    ( spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f131,f121])).

fof(f121,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f63,f68,f73,f88,f100,f112,f46])).

fof(f46,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f112,plain,
    ( m1_subset_1(o_2_2_yellow_6(sK0,sK1),u1_struct_0(sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_9
  <=> m1_subset_1(o_2_2_yellow_6(sK0,sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f100,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f43,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f88,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f73,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f68,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f63,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f131,plain,
    ( r2_waybel_0(sK0,sK1,k1_xboole_0)
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | spl4_8 ),
    inference(backward_demodulation,[],[f114,f126])).

fof(f126,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f93,f104,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f104,plain,(
    ! [X0] : v1_xboole_0(k6_subset_1(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f59,f58,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f51,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f93,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f114,plain,
    ( r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_6
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f63,f73,f98,f88,f68,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r1_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ~ r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f98,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_8
  <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f113,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f106,f86,f81,f76,f71,f66,f61,f110])).

fof(f76,plain,
    ( spl4_4
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f81,plain,
    ( spl4_5
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f106,plain,
    ( m1_subset_1(o_2_2_yellow_6(sK0,sK1),u1_struct_0(sK1))
    | spl4_1
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f63,f68,f73,f78,f83,f88,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1))
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
     => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

fof(f83,plain,
    ( v7_waybel_0(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f78,plain,
    ( v4_orders_2(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f99,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f41,f96])).

fof(f41,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f94,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f89,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f40,f86])).

fof(f40,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f39,f81])).

fof(f39,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (2463)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (2457)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (2450)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (2451)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (2455)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (2453)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (2463)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f136,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f84,f89,f94,f99,f113,f133])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    spl4_1 | ~spl4_2 | spl4_3 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_9),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f132])).
% 0.21/0.46  fof(f132,plain,(
% 0.21/0.46    $false | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_6 | ~spl4_7 | spl4_8 | ~spl4_9)),
% 0.21/0.46    inference(subsumption_resolution,[],[f131,f121])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ~r2_waybel_0(sK0,sK1,k1_xboole_0) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_6 | ~spl4_9)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f63,f68,f73,f88,f100,f112,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    ( ! [X2,X0,X5,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | v2_struct_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f30,f32,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(rectify,[],[f29])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,axiom,(
% 0.21/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    m1_subset_1(o_2_2_yellow_6(sK0,sK1),u1_struct_0(sK1)) | ~spl4_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f110])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl4_9 <=> m1_subset_1(o_2_2_yellow_6(sK0,sK1),u1_struct_0(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f43,f57])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    l1_waybel_0(sK1,sK0) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f86])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl4_6 <=> l1_waybel_0(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    ~v2_struct_0(sK1) | spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    spl4_3 <=> v2_struct_0(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    l1_struct_0(sK0) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl4_2 <=> l1_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    r2_waybel_0(sK0,sK1,k1_xboole_0) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_6 | ~spl4_7 | spl4_8)),
% 0.21/0.46    inference(backward_demodulation,[],[f114,f126])).
% 0.21/0.46  fof(f126,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) ) | ~spl4_7),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f93,f104,f56])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    ( ! [X0] : (v1_xboole_0(k6_subset_1(X0,X0))) )),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f59,f58,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f51,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f52,f53])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0) | ~spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f91])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl4_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    r2_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_6 | spl4_8)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f63,f73,f98,f88,f68,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r1_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ~r2_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_waybel_0)).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | spl4_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl4_8 <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl4_9 | spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f106,f86,f81,f76,f71,f66,f61,f110])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl4_4 <=> v4_orders_2(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl4_5 <=> v7_waybel_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    m1_subset_1(o_2_2_yellow_6(sK0,sK1),u1_struct_0(sK1)) | (spl4_1 | ~spl4_2 | spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f63,f68,f73,f78,f83,f88,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(o_2_2_yellow_6(X0,X1),u1_struct_0(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    v7_waybel_0(sK1) | ~spl4_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    v4_orders_2(sK1) | ~spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ~spl4_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f96])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f27,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl4_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f91])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f86])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    l1_waybel_0(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f81])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    v7_waybel_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl4_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f76])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    v4_orders_2(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ~spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f71])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f66])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f61])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (2463)------------------------------
% 0.21/0.47  % (2463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2463)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (2463)Memory used [KB]: 10746
% 0.21/0.47  % (2463)Time elapsed: 0.011 s
% 0.21/0.47  % (2463)------------------------------
% 0.21/0.47  % (2463)------------------------------
% 0.21/0.47  % (2451)Refutation not found, incomplete strategy% (2451)------------------------------
% 0.21/0.47  % (2451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2451)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (2451)Memory used [KB]: 1663
% 0.21/0.47  % (2451)Time elapsed: 0.061 s
% 0.21/0.47  % (2451)------------------------------
% 0.21/0.47  % (2451)------------------------------
% 0.21/0.47  % (2444)Success in time 0.113 s
%------------------------------------------------------------------------------
