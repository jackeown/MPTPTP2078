%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 139 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  358 ( 667 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f78,f83,f87,f91,f95,f99,f112,f120,f136,f149,f153])).

fof(f153,plain,
    ( spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f138,f150])).

fof(f150,plain,
    ( r2_waybel_0(sK0,sK1,k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_6
    | spl5_7
    | ~ spl5_21 ),
    inference(unit_resulting_resolution,[],[f52,f57,f62,f77,f82,f148])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( r1_waybel_0(X0,X1,u1_struct_0(X0))
        | r2_waybel_0(X0,X1,k1_xboole_0)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( r1_waybel_0(X0,X1,u1_struct_0(X0))
        | r2_waybel_0(X0,X1,k1_xboole_0)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f82,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_7
  <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f77,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f62,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl5_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f57,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f52,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f138,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | spl5_1
    | ~ spl5_2
    | spl5_3
    | ~ spl5_6
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f52,f57,f62,f77,f90,f119,f135])).

fof(f135,plain,
    ( ! [X2,X0,X5,X1] :
        ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ r2_waybel_0(X0,X1,X2)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_19
  <=> ! [X1,X5,X0,X2] :
        ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ r2_waybel_0(X0,X1,X2)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f119,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl5_16
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f90,plain,
    ( ! [X0] : m1_subset_1(sK4(X0),X0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_9
  <=> ! [X0] : m1_subset_1(sK4(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f149,plain,
    ( spl5_21
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f121,f110,f93,f147])).

fof(f93,plain,
    ( spl5_10
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f110,plain,
    ( spl5_14
  <=> ! [X1,X0,X2] :
        ( r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
        | r2_waybel_0(X0,X1,X2)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( r1_waybel_0(X0,X1,u1_struct_0(X0))
        | r2_waybel_0(X0,X1,k1_xboole_0)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl5_10
    | ~ spl5_14 ),
    inference(superposition,[],[f111,f94])).

fof(f94,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f111,plain,
    ( ! [X2,X0,X1] :
        ( r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
        | r2_waybel_0(X0,X1,X2)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f136,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f41,f134])).

fof(f41,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f24,f23])).

fof(f23,plain,(
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

fof(f24,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f120,plain,
    ( spl5_16
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f104,f97,f85,f118])).

fof(f85,plain,
    ( spl5_8
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f97,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(unit_resulting_resolution,[],[f86,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f86,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f112,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f47,f110])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f38,f45])).

fof(f45,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
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
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f99,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f46,f97])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f95,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f36,f93])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f91,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f44,f89])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f87,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f35,f85])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f83,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).

fof(f17,plain,
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

fof(f18,plain,
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

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f78,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f33,f75])).

fof(f33,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f55])).

fof(f29,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f28,f50])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:51:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (11771)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.41  % (11771)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f154,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f53,f58,f63,f78,f83,f87,f91,f95,f99,f112,f120,f136,f149,f153])).
% 0.21/0.42  fof(f153,plain,(
% 0.21/0.42    spl5_1 | ~spl5_2 | spl5_3 | ~spl5_6 | spl5_7 | ~spl5_9 | ~spl5_16 | ~spl5_19 | ~spl5_21),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    $false | (spl5_1 | ~spl5_2 | spl5_3 | ~spl5_6 | spl5_7 | ~spl5_9 | ~spl5_16 | ~spl5_19 | ~spl5_21)),
% 0.21/0.42    inference(subsumption_resolution,[],[f138,f150])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    r2_waybel_0(sK0,sK1,k1_xboole_0) | (spl5_1 | ~spl5_2 | spl5_3 | ~spl5_6 | spl5_7 | ~spl5_21)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f52,f57,f62,f77,f82,f148])).
% 0.21/0.42  fof(f148,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_waybel_0(X0,X1,u1_struct_0(X0)) | r2_waybel_0(X0,X1,k1_xboole_0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl5_21),
% 0.21/0.42    inference(avatar_component_clause,[],[f147])).
% 0.21/0.42  fof(f147,plain,(
% 0.21/0.42    spl5_21 <=> ! [X1,X0] : (r1_waybel_0(X0,X1,u1_struct_0(X0)) | r2_waybel_0(X0,X1,k1_xboole_0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | spl5_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f80])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    spl5_7 <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    l1_waybel_0(sK1,sK0) | ~spl5_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f75])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    spl5_6 <=> l1_waybel_0(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ~v2_struct_0(sK1) | spl5_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f60])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl5_3 <=> v2_struct_0(sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    l1_struct_0(sK0) | ~spl5_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    spl5_2 <=> l1_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    ~v2_struct_0(sK0) | spl5_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl5_1 <=> v2_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.42  fof(f138,plain,(
% 0.21/0.42    ~r2_waybel_0(sK0,sK1,k1_xboole_0) | (spl5_1 | ~spl5_2 | spl5_3 | ~spl5_6 | ~spl5_9 | ~spl5_16 | ~spl5_19)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f52,f57,f62,f77,f90,f119,f135])).
% 0.21/0.42  fof(f135,plain,(
% 0.21/0.42    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl5_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f134])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    spl5_19 <=> ! [X1,X5,X0,X2] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f118])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    spl5_16 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) ) | ~spl5_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f89])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl5_9 <=> ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.42  fof(f149,plain,(
% 0.21/0.42    spl5_21 | ~spl5_10 | ~spl5_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f121,f110,f93,f147])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl5_10 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    spl5_14 <=> ! [X1,X0,X2] : (r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_waybel_0(X0,X1,u1_struct_0(X0)) | r2_waybel_0(X0,X1,k1_xboole_0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | (~spl5_10 | ~spl5_14)),
% 0.21/0.42    inference(superposition,[],[f111,f94])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl5_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f93])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl5_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f110])).
% 0.21/0.42  fof(f136,plain,(
% 0.21/0.42    spl5_19),
% 0.21/0.42    inference(avatar_split_clause,[],[f41,f134])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f22,f24,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(rectify,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(nnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    spl5_16 | ~spl5_8 | ~spl5_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f104,f97,f85,f118])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    spl5_8 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    spl5_11 <=> ! [X1,X0] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_8 | ~spl5_11)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f86,f98])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl5_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f97])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl5_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f85])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    spl5_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f47,f110])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.42    inference(forward_demodulation,[],[f38,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(nnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    spl5_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f46,f97])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    spl5_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f36,f93])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl5_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f44,f89])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl5_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f35,f85])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    ~spl5_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f34,f80])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl5_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f33,f75])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    l1_waybel_0(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ~spl5_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f60])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ~v2_struct_0(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl5_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f55])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    l1_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ~spl5_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f50])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ~v2_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f19])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (11771)------------------------------
% 0.21/0.42  % (11771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (11771)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (11771)Memory used [KB]: 6140
% 0.21/0.42  % (11771)Time elapsed: 0.008 s
% 0.21/0.42  % (11771)------------------------------
% 0.21/0.42  % (11771)------------------------------
% 0.21/0.42  % (11763)Success in time 0.064 s
%------------------------------------------------------------------------------
