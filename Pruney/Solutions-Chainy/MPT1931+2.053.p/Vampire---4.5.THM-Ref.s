%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 135 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  351 ( 639 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f97,f102,f171,f196])).

fof(f196,plain,
    ( spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | spl6_7
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | spl6_7
    | spl6_10 ),
    inference(subsumption_resolution,[],[f194,f101])).

fof(f101,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_7
  <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f194,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | spl6_10 ),
    inference(forward_demodulation,[],[f184,f49])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f184,plain,
    ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),k1_xboole_0))
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f81,f96,f170,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK0)
        | r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1))
        | v2_struct_0(X0)
        | r2_waybel_0(sK0,X0,X1) )
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f124,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1))
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | r2_waybel_0(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f66,f76])).

fof(f76,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl6_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f60,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

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

fof(f170,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_10
  <=> r2_waybel_0(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f96,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f81,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f171,plain,
    ( ~ spl6_10
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f149,f94,f79,f74,f69,f168])).

fof(f149,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f71,f76,f81,f96,f103,f144,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ r1_tarski(X2,X3)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

fof(f144,plain,
    ( ! [X0] : ~ r2_waybel_0(sK0,sK1,k3_xboole_0(X0,k1_xboole_0))
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f71,f76,f81,f96,f59,f108,f54])).

fof(f54,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).

fof(f32,plain,(
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

fof(f33,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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

fof(f108,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f47,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f47,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f103,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f48,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f102,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f46,f99])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f27,f26])).

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

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

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

fof(f97,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f45,f94])).

fof(f45,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f42,f79])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f40,f69])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:16:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (314)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.43  % (325)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.44  % (325)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f197,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f72,f77,f82,f97,f102,f171,f196])).
% 0.22/0.44  fof(f196,plain,(
% 0.22/0.44    spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | spl6_7 | spl6_10),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f195])).
% 0.22/0.44  fof(f195,plain,(
% 0.22/0.44    $false | (spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | spl6_7 | spl6_10)),
% 0.22/0.44    inference(subsumption_resolution,[],[f194,f101])).
% 0.22/0.44  fof(f101,plain,(
% 0.22/0.44    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | spl6_7),
% 0.22/0.44    inference(avatar_component_clause,[],[f99])).
% 0.22/0.44  fof(f99,plain,(
% 0.22/0.44    spl6_7 <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.44  fof(f194,plain,(
% 0.22/0.44    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | (spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | spl6_10)),
% 0.22/0.44    inference(forward_demodulation,[],[f184,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.44  fof(f184,plain,(
% 0.22/0.44    r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),k1_xboole_0)) | (spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | spl6_10)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f81,f96,f170,f125])).
% 0.22/0.44  fof(f125,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1)) | v2_struct_0(X0) | r2_waybel_0(sK0,X0,X1)) ) | (spl6_1 | ~spl6_2)),
% 0.22/0.44    inference(subsumption_resolution,[],[f124,f71])).
% 0.22/0.44  fof(f71,plain,(
% 0.22/0.44    ~v2_struct_0(sK0) | spl6_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f69])).
% 0.22/0.44  fof(f69,plain,(
% 0.22/0.44    spl6_1 <=> v2_struct_0(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.44  fof(f124,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1)) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r2_waybel_0(sK0,X0,X1) | v2_struct_0(sK0)) ) | ~spl6_2),
% 0.22/0.44    inference(resolution,[],[f66,f76])).
% 0.22/0.44  fof(f76,plain,(
% 0.22/0.44    l1_struct_0(sK0) | ~spl6_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f74])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl6_2 <=> l1_struct_0(sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f51,f60])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(nnf_transformation,[],[f18])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.22/0.44  fof(f170,plain,(
% 0.22/0.44    ~r2_waybel_0(sK0,sK1,k1_xboole_0) | spl6_10),
% 0.22/0.44    inference(avatar_component_clause,[],[f168])).
% 0.22/0.44  fof(f168,plain,(
% 0.22/0.44    spl6_10 <=> r2_waybel_0(sK0,sK1,k1_xboole_0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.44  fof(f96,plain,(
% 0.22/0.44    l1_waybel_0(sK1,sK0) | ~spl6_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f94])).
% 0.22/0.44  fof(f94,plain,(
% 0.22/0.44    spl6_6 <=> l1_waybel_0(sK1,sK0)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    ~v2_struct_0(sK1) | spl6_3),
% 0.22/0.44    inference(avatar_component_clause,[],[f79])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    spl6_3 <=> v2_struct_0(sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.44  fof(f171,plain,(
% 0.22/0.44    ~spl6_10 | spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f149,f94,f79,f74,f69,f168])).
% 0.22/0.44  fof(f149,plain,(
% 0.22/0.44    ~r2_waybel_0(sK0,sK1,k1_xboole_0) | (spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f71,f76,f81,f96,f103,f144,f58])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (~l1_struct_0(X0) | ~r2_waybel_0(X0,X1,X2) | ~r1_tarski(X2,X3) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X3) | v2_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,axiom,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (r1_tarski(X2,X3) => ((r2_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X3)) & (r1_waybel_0(X0,X1,X2) => r1_waybel_0(X0,X1,X3))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).
% 0.22/0.44  fof(f144,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_waybel_0(sK0,sK1,k3_xboole_0(X0,k1_xboole_0))) ) | (spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6)),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f71,f76,f81,f96,f59,f108,f54])).
% 0.22/0.44  fof(f54,plain,(
% 0.22/0.44    ( ! [X2,X0,X5,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | v2_struct_0(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(rectify,[],[f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(nnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f19])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f47,f62])).
% 0.22/0.44  fof(f62,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(rectify,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f36])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.22/0.44  fof(f103,plain,(
% 0.22/0.44    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.44    inference(unit_resulting_resolution,[],[f48,f63])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f39])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.44    inference(nnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    ~spl6_7),
% 0.22/0.44    inference(avatar_split_clause,[],[f46,f99])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f27,f26])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.44    inference(flattening,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.44    inference(ennf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,negated_conjecture,(
% 0.22/0.44    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.44    inference(negated_conjecture,[],[f12])).
% 0.22/0.44  fof(f12,conjecture,(
% 0.22/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    spl6_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f45,f94])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    l1_waybel_0(sK1,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f28])).
% 0.22/0.44  fof(f82,plain,(
% 0.22/0.44    ~spl6_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f42,f79])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ~v2_struct_0(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f28])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    spl6_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f41,f74])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    l1_struct_0(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f28])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    ~spl6_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f40,f69])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ~v2_struct_0(sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f28])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (325)------------------------------
% 0.22/0.44  % (325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (325)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (325)Memory used [KB]: 10746
% 0.22/0.44  % (325)Time elapsed: 0.009 s
% 0.22/0.44  % (325)------------------------------
% 0.22/0.44  % (325)------------------------------
% 0.22/0.44  % (308)Success in time 0.079 s
%------------------------------------------------------------------------------
