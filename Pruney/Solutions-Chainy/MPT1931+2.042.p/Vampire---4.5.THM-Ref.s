%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:43 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 148 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  352 ( 667 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f80,f85,f90,f95,f108,f113,f124,f154,f175])).

fof(f175,plain,
    ( ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_13
    | spl5_17 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_13
    | spl5_17 ),
    inference(unit_resulting_resolution,[],[f89,f84,f79,f64,f123,f40,f153,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_waybel_0(X0,X1,X2)
      | r2_waybel_0(X0,X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f153,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK4(k1_zfmisc_1(k1_xboole_0)))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl5_17
  <=> r2_waybel_0(sK0,sK1,sK4(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f123,plain,
    ( r2_waybel_0(sK0,sK1,k1_xboole_0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl5_13
  <=> r2_waybel_0(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f64,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_2
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f79,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_5
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f84,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f89,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f154,plain,
    ( ~ spl5_17
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f148,f92,f87,f82,f77,f62,f151])).

fof(f92,plain,
    ( spl5_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f148,plain,
    ( ~ r2_waybel_0(sK0,sK1,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_2
    | spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f89,f84,f79,f64,f51,f96,f46])).

fof(f46,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f96,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f94,f51,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f94,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f124,plain,
    ( spl5_13
    | spl5_1
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f115,f111,f57,f121])).

fof(f57,plain,
    ( spl5_1
  <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f111,plain,
    ( spl5_11
  <=> ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f115,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | r2_waybel_0(sK0,sK1,k1_xboole_0)
    | ~ spl5_11 ),
    inference(superposition,[],[f112,f41])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f112,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0))
        | r2_waybel_0(sK0,sK1,X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl5_5
    | spl5_11
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f109,f106,f62,f111,f77])).

fof(f106,plain,
    ( spl5_10
  <=> ! [X1,X0] :
        ( r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1))
        | r2_waybel_0(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f109,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | v2_struct_0(sK1)
        | r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0)) )
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(resolution,[],[f107,f64])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK0)
        | r2_waybel_0(sK0,X0,X1)
        | v2_struct_0(X0)
        | r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1)) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,
    ( spl5_7
    | spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f104,f82,f106,f87])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1))
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | r2_waybel_0(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f54,f84])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f43,f52])).

fof(f52,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
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
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f95,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f39,f92])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f32,f87])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).

fof(f21,plain,
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

fof(f22,plain,
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

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f85,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f62])).

fof(f37,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f57])).

fof(f38,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n009.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:16:11 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.44  % (10696)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.44  % (10693)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.18/0.45  % (10697)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.18/0.45  % (10695)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.45  % (10703)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.18/0.45  % (10707)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.18/0.45  % (10698)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.18/0.46  % (10698)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f176,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(avatar_sat_refutation,[],[f60,f65,f80,f85,f90,f95,f108,f113,f124,f154,f175])).
% 0.18/0.46  fof(f175,plain,(
% 0.18/0.46    ~spl5_2 | spl5_5 | ~spl5_6 | spl5_7 | ~spl5_13 | spl5_17),
% 0.18/0.46    inference(avatar_contradiction_clause,[],[f173])).
% 0.18/0.46  fof(f173,plain,(
% 0.18/0.46    $false | (~spl5_2 | spl5_5 | ~spl5_6 | spl5_7 | ~spl5_13 | spl5_17)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f89,f84,f79,f64,f123,f40,f153,f50])).
% 0.18/0.46  fof(f50,plain,(
% 0.18/0.46    ( ! [X2,X0,X3,X1] : (~r2_waybel_0(X0,X1,X2) | r2_waybel_0(X0,X1,X3) | ~r1_tarski(X2,X3) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f19])).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f18])).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2,X3] : (((r2_waybel_0(X0,X1,X3) | ~r2_waybel_0(X0,X1,X2)) & (r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2))) | ~r1_tarski(X2,X3)) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f9])).
% 0.18/0.46  fof(f9,axiom,(
% 0.18/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2,X3] : (r1_tarski(X2,X3) => ((r2_waybel_0(X0,X1,X2) => r2_waybel_0(X0,X1,X3)) & (r1_waybel_0(X0,X1,X2) => r1_waybel_0(X0,X1,X3))))))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).
% 0.18/0.46  fof(f153,plain,(
% 0.18/0.46    ~r2_waybel_0(sK0,sK1,sK4(k1_zfmisc_1(k1_xboole_0))) | spl5_17),
% 0.18/0.46    inference(avatar_component_clause,[],[f151])).
% 0.18/0.46  fof(f151,plain,(
% 0.18/0.46    spl5_17 <=> r2_waybel_0(sK0,sK1,sK4(k1_zfmisc_1(k1_xboole_0)))),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.18/0.46  fof(f40,plain,(
% 0.18/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.46  fof(f123,plain,(
% 0.18/0.46    r2_waybel_0(sK0,sK1,k1_xboole_0) | ~spl5_13),
% 0.18/0.46    inference(avatar_component_clause,[],[f121])).
% 0.18/0.46  fof(f121,plain,(
% 0.18/0.46    spl5_13 <=> r2_waybel_0(sK0,sK1,k1_xboole_0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.18/0.46  fof(f64,plain,(
% 0.18/0.46    l1_waybel_0(sK1,sK0) | ~spl5_2),
% 0.18/0.46    inference(avatar_component_clause,[],[f62])).
% 0.18/0.46  fof(f62,plain,(
% 0.18/0.46    spl5_2 <=> l1_waybel_0(sK1,sK0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.18/0.46  fof(f79,plain,(
% 0.18/0.46    ~v2_struct_0(sK1) | spl5_5),
% 0.18/0.46    inference(avatar_component_clause,[],[f77])).
% 0.18/0.46  fof(f77,plain,(
% 0.18/0.46    spl5_5 <=> v2_struct_0(sK1)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.18/0.46  fof(f84,plain,(
% 0.18/0.46    l1_struct_0(sK0) | ~spl5_6),
% 0.18/0.46    inference(avatar_component_clause,[],[f82])).
% 0.18/0.46  fof(f82,plain,(
% 0.18/0.46    spl5_6 <=> l1_struct_0(sK0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.18/0.46  fof(f89,plain,(
% 0.18/0.46    ~v2_struct_0(sK0) | spl5_7),
% 0.18/0.46    inference(avatar_component_clause,[],[f87])).
% 0.18/0.46  fof(f87,plain,(
% 0.18/0.46    spl5_7 <=> v2_struct_0(sK0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.18/0.46  fof(f154,plain,(
% 0.18/0.46    ~spl5_17 | ~spl5_2 | spl5_5 | ~spl5_6 | spl5_7 | ~spl5_8),
% 0.18/0.46    inference(avatar_split_clause,[],[f148,f92,f87,f82,f77,f62,f151])).
% 0.18/0.46  fof(f92,plain,(
% 0.18/0.46    spl5_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.18/0.46  fof(f148,plain,(
% 0.18/0.46    ~r2_waybel_0(sK0,sK1,sK4(k1_zfmisc_1(k1_xboole_0))) | (~spl5_2 | spl5_5 | ~spl5_6 | spl5_7 | ~spl5_8)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f89,f84,f79,f64,f51,f96,f46])).
% 0.18/0.46  fof(f46,plain,(
% 0.18/0.46    ( ! [X2,X0,X5,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | v2_struct_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f29])).
% 0.18/0.46  fof(f29,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f28,f27])).
% 0.18/0.46  fof(f27,plain,(
% 0.18/0.46    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f28,plain,(
% 0.18/0.46    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f26,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(rectify,[],[f25])).
% 0.18/0.46  fof(f25,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(nnf_transformation,[],[f17])).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f16])).
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f7])).
% 0.18/0.46  fof(f7,axiom,(
% 0.18/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.18/0.46  fof(f96,plain,(
% 0.18/0.46    ( ! [X0] : (~r2_hidden(X0,sK4(k1_zfmisc_1(k1_xboole_0)))) ) | ~spl5_8),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f94,f51,f53])).
% 0.18/0.46  fof(f53,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f6])).
% 0.18/0.46  fof(f6,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.18/0.46  fof(f94,plain,(
% 0.18/0.46    v1_xboole_0(k1_xboole_0) | ~spl5_8),
% 0.18/0.46    inference(avatar_component_clause,[],[f92])).
% 0.18/0.46  fof(f51,plain,(
% 0.18/0.46    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f31])).
% 0.18/0.46  fof(f31,plain,(
% 0.18/0.46    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.18/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f30])).
% 0.18/0.46  fof(f30,plain,(
% 0.18/0.46    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.18/0.46  fof(f124,plain,(
% 0.18/0.46    spl5_13 | spl5_1 | ~spl5_11),
% 0.18/0.46    inference(avatar_split_clause,[],[f115,f111,f57,f121])).
% 0.18/0.46  fof(f57,plain,(
% 0.18/0.46    spl5_1 <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.18/0.46  fof(f111,plain,(
% 0.18/0.46    spl5_11 <=> ! [X0] : (r2_waybel_0(sK0,sK1,X0) | r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0)))),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.18/0.46  fof(f115,plain,(
% 0.18/0.46    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | r2_waybel_0(sK0,sK1,k1_xboole_0) | ~spl5_11),
% 0.18/0.46    inference(superposition,[],[f112,f41])).
% 0.18/0.46  fof(f41,plain,(
% 0.18/0.46    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.46    inference(cnf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.18/0.46  fof(f112,plain,(
% 0.18/0.46    ( ! [X0] : (r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0)) | r2_waybel_0(sK0,sK1,X0)) ) | ~spl5_11),
% 0.18/0.46    inference(avatar_component_clause,[],[f111])).
% 0.18/0.46  fof(f113,plain,(
% 0.18/0.46    spl5_5 | spl5_11 | ~spl5_2 | ~spl5_10),
% 0.18/0.46    inference(avatar_split_clause,[],[f109,f106,f62,f111,f77])).
% 0.18/0.46  fof(f106,plain,(
% 0.18/0.46    spl5_10 <=> ! [X1,X0] : (r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,X0,X1) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0))),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.18/0.46  fof(f109,plain,(
% 0.18/0.46    ( ! [X0] : (r2_waybel_0(sK0,sK1,X0) | v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,k4_xboole_0(u1_struct_0(sK0),X0))) ) | (~spl5_2 | ~spl5_10)),
% 0.18/0.46    inference(resolution,[],[f107,f64])).
% 0.18/0.46  fof(f107,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | r2_waybel_0(sK0,X0,X1) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1))) ) | ~spl5_10),
% 0.18/0.46    inference(avatar_component_clause,[],[f106])).
% 0.18/0.46  fof(f108,plain,(
% 0.18/0.46    spl5_7 | spl5_10 | ~spl5_6),
% 0.18/0.46    inference(avatar_split_clause,[],[f104,f82,f106,f87])).
% 0.18/0.46  fof(f104,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r1_waybel_0(sK0,X0,k4_xboole_0(u1_struct_0(sK0),X1)) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r2_waybel_0(sK0,X0,X1) | v2_struct_0(sK0)) ) | ~spl5_6),
% 0.18/0.46    inference(resolution,[],[f54,f84])).
% 0.18/0.46  fof(f54,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.18/0.46    inference(definition_unfolding,[],[f43,f52])).
% 0.18/0.46  fof(f52,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f5])).
% 0.18/0.46  fof(f5,axiom,(
% 0.18/0.46    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.18/0.46  fof(f43,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f24])).
% 0.18/0.46  fof(f24,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(nnf_transformation,[],[f15])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f14])).
% 0.18/0.46  fof(f14,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f8])).
% 0.18/0.46  fof(f8,axiom,(
% 0.18/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.18/0.46  fof(f95,plain,(
% 0.18/0.46    spl5_8),
% 0.18/0.46    inference(avatar_split_clause,[],[f39,f92])).
% 0.18/0.46  fof(f39,plain,(
% 0.18/0.46    v1_xboole_0(k1_xboole_0)),
% 0.18/0.46    inference(cnf_transformation,[],[f1])).
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    v1_xboole_0(k1_xboole_0)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.18/0.46  fof(f90,plain,(
% 0.18/0.46    ~spl5_7),
% 0.18/0.46    inference(avatar_split_clause,[],[f32,f87])).
% 0.18/0.46  fof(f32,plain,(
% 0.18/0.46    ~v2_struct_0(sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f23])).
% 0.18/0.46  fof(f23,plain,(
% 0.18/0.46    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.18/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f12])).
% 0.18/0.46  fof(f12,plain,(
% 0.18/0.46    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f11])).
% 0.18/0.46  fof(f11,negated_conjecture,(
% 0.18/0.46    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.18/0.46    inference(negated_conjecture,[],[f10])).
% 0.18/0.46  fof(f10,conjecture,(
% 0.18/0.46    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.18/0.46  fof(f85,plain,(
% 0.18/0.46    spl5_6),
% 0.18/0.46    inference(avatar_split_clause,[],[f33,f82])).
% 0.18/0.46  fof(f33,plain,(
% 0.18/0.46    l1_struct_0(sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f23])).
% 0.18/0.46  fof(f80,plain,(
% 0.18/0.46    ~spl5_5),
% 0.18/0.46    inference(avatar_split_clause,[],[f34,f77])).
% 0.18/0.46  fof(f34,plain,(
% 0.18/0.46    ~v2_struct_0(sK1)),
% 0.18/0.46    inference(cnf_transformation,[],[f23])).
% 0.18/0.46  fof(f65,plain,(
% 0.18/0.46    spl5_2),
% 0.18/0.46    inference(avatar_split_clause,[],[f37,f62])).
% 0.18/0.46  fof(f37,plain,(
% 0.18/0.46    l1_waybel_0(sK1,sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f23])).
% 0.18/0.46  fof(f60,plain,(
% 0.18/0.46    ~spl5_1),
% 0.18/0.46    inference(avatar_split_clause,[],[f38,f57])).
% 0.18/0.46  fof(f38,plain,(
% 0.18/0.46    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.18/0.46    inference(cnf_transformation,[],[f23])).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (10698)------------------------------
% 0.18/0.46  % (10698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (10698)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (10698)Memory used [KB]: 6140
% 0.18/0.46  % (10698)Time elapsed: 0.061 s
% 0.18/0.46  % (10698)------------------------------
% 0.18/0.46  % (10698)------------------------------
% 0.18/0.46  % (10704)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.18/0.46  % (10691)Success in time 0.114 s
%------------------------------------------------------------------------------
