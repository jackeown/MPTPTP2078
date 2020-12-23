%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 177 expanded)
%              Number of leaves         :   33 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  441 ( 795 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f296,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f94,f99,f104,f108,f112,f124,f128,f140,f161,f165,f189,f217,f248,f293,f295])).

fof(f295,plain,
    ( spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | spl6_7
    | spl6_29
    | ~ spl6_33
    | ~ spl6_40 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | spl6_7
    | spl6_29
    | ~ spl6_33
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f251,f292])).

fof(f292,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl6_40
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f251,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK0),k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | spl6_7
    | spl6_29
    | ~ spl6_33 ),
    inference(unit_resulting_resolution,[],[f78,f68,f73,f93,f216,f98,f247])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( r1_waybel_0(X0,X2,u1_struct_0(X0))
        | r2_waybel_0(X0,X2,X1)
        | ~ l1_waybel_0(X2,X0)
        | v2_struct_0(X2)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0)
        | ~ r1_xboole_0(u1_struct_0(X0),X1) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl6_33
  <=> ! [X1,X0,X2] :
        ( r1_waybel_0(X0,X2,u1_struct_0(X0))
        | r2_waybel_0(X0,X2,X1)
        | ~ l1_waybel_0(X2,X0)
        | v2_struct_0(X2)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0)
        | ~ r1_xboole_0(u1_struct_0(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f98,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_7
  <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f216,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl6_29
  <=> r2_waybel_0(sK0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f93,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl6_6
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f73,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f68,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f78,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f76])).

% (28591)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f76,plain,
    ( spl6_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f293,plain,
    ( spl6_40
    | ~ spl6_13
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f183,f159,f122,f291])).

fof(f122,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f159,plain,
    ( spl6_20
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f183,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl6_13
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f160,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f160,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f159])).

fof(f248,plain,
    ( spl6_33
    | ~ spl6_14
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f170,f163,f126,f246])).

fof(f126,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f163,plain,
    ( spl6_21
  <=> ! [X1,X0,X2] :
        ( r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
        | r2_waybel_0(X0,X1,X2)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( r1_waybel_0(X0,X2,u1_struct_0(X0))
        | r2_waybel_0(X0,X2,X1)
        | ~ l1_waybel_0(X2,X0)
        | v2_struct_0(X2)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0)
        | ~ r1_xboole_0(u1_struct_0(X0),X1) )
    | ~ spl6_14
    | ~ spl6_21 ),
    inference(superposition,[],[f164,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f164,plain,
    ( ! [X2,X0,X1] :
        ( r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
        | r2_waybel_0(X0,X1,X2)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f163])).

fof(f217,plain,
    ( ~ spl6_29
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f190,f187,f159,f110,f91,f76,f71,f66,f214])).

fof(f110,plain,
    ( spl6_10
  <=> ! [X0] : m1_subset_1(sK4(X0),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f187,plain,
    ( spl6_25
  <=> ! [X1,X5,X0,X2] :
        ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ r2_waybel_0(X0,X1,X2)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f190,plain,
    ( ~ r2_waybel_0(sK0,sK1,k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | spl6_3
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f68,f73,f78,f93,f111,f160,f188])).

fof(f188,plain,
    ( ! [X2,X0,X5,X1] :
        ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        | ~ m1_subset_1(X5,u1_struct_0(X1))
        | ~ r2_waybel_0(X0,X1,X2)
        | ~ l1_waybel_0(X1,X0)
        | v2_struct_0(X1)
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f187])).

fof(f111,plain,
    ( ! [X0] : m1_subset_1(sK4(X0),X0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f189,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f51,f187])).

fof(f51,plain,(
    ! [X2,X0,X5,X1] :
      ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f31,f30])).

fof(f30,plain,(
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

fof(f31,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f165,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f63,f163])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2))
      | r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f48,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

% (28583)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f161,plain,
    ( spl6_20
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f148,f138,f106,f101,f159])).

fof(f101,plain,
    ( spl6_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f106,plain,
    ( spl6_9
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f138,plain,
    ( spl6_17
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f148,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f103,f107,f139])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f107,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f103,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f140,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f62,f138])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

% (28579)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f128,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f59,f126])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f124,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f57,f122])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f112,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f54,f110])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f108,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f46,f106])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f104,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f45,f101])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f99,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).

% (28576)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% (28580)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% (28594)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f24,plain,
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

fof(f25,plain,
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f94,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f43,f91])).

fof(f43,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f40,f76])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f38,f66])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:01:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (28581)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (28581)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (28578)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f296,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f69,f74,f79,f94,f99,f104,f108,f112,f124,f128,f140,f161,f165,f189,f217,f248,f293,f295])).
% 0.20/0.47  fof(f295,plain,(
% 0.20/0.47    spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | spl6_7 | spl6_29 | ~spl6_33 | ~spl6_40),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f294])).
% 0.20/0.47  fof(f294,plain,(
% 0.20/0.47    $false | (spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | spl6_7 | spl6_29 | ~spl6_33 | ~spl6_40)),
% 0.20/0.47    inference(subsumption_resolution,[],[f251,f292])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl6_40),
% 0.20/0.47    inference(avatar_component_clause,[],[f291])).
% 0.20/0.47  fof(f291,plain,(
% 0.20/0.47    spl6_40 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    ~r1_xboole_0(u1_struct_0(sK0),k1_xboole_0) | (spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | spl6_7 | spl6_29 | ~spl6_33)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f78,f68,f73,f93,f216,f98,f247])).
% 0.20/0.47  fof(f247,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X2,u1_struct_0(X0)) | r2_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~r1_xboole_0(u1_struct_0(X0),X1)) ) | ~spl6_33),
% 0.20/0.47    inference(avatar_component_clause,[],[f246])).
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    spl6_33 <=> ! [X1,X0,X2] : (r1_waybel_0(X0,X2,u1_struct_0(X0)) | r2_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~r1_xboole_0(u1_struct_0(X0),X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | spl6_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f96])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl6_7 <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    ~r2_waybel_0(sK0,sK1,k1_xboole_0) | spl6_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f214])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    spl6_29 <=> r2_waybel_0(sK0,sK1,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    l1_waybel_0(sK1,sK0) | ~spl6_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f91])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    spl6_6 <=> l1_waybel_0(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    l1_struct_0(sK0) | ~spl6_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl6_2 <=> l1_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ~v2_struct_0(sK0) | spl6_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl6_1 <=> v2_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    ~v2_struct_0(sK1) | spl6_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  % (28591)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl6_3 <=> v2_struct_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.47  fof(f293,plain,(
% 0.20/0.47    spl6_40 | ~spl6_13 | ~spl6_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f183,f159,f122,f291])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl6_13 <=> ! [X1,X0] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    spl6_20 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.47  fof(f183,plain,(
% 0.20/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | (~spl6_13 | ~spl6_20)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f160,f123])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl6_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f122])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f159])).
% 0.20/0.47  fof(f248,plain,(
% 0.20/0.47    spl6_33 | ~spl6_14 | ~spl6_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f170,f163,f126,f246])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl6_14 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl6_21 <=> ! [X1,X0,X2] : (r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X2,u1_struct_0(X0)) | r2_waybel_0(X0,X2,X1) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~r1_xboole_0(u1_struct_0(X0),X1)) ) | (~spl6_14 | ~spl6_21)),
% 0.20/0.47    inference(superposition,[],[f164,f127])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl6_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f126])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl6_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f163])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    ~spl6_29 | spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | ~spl6_10 | ~spl6_20 | ~spl6_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f190,f187,f159,f110,f91,f76,f71,f66,f214])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    spl6_10 <=> ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    spl6_25 <=> ! [X1,X5,X0,X2] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    ~r2_waybel_0(sK0,sK1,k1_xboole_0) | (spl6_1 | ~spl6_2 | spl6_3 | ~spl6_6 | ~spl6_10 | ~spl6_20 | ~spl6_25)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f68,f73,f78,f93,f111,f160,f188])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl6_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f187])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) ) | ~spl6_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f110])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    spl6_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f51,f187])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X5,X1] : (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f29,f31,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(rectify,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl6_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f63,f163])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,k4_xboole_0(u1_struct_0(X0),X2)) | r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f48,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  % (28583)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl6_20 | ~spl6_8 | ~spl6_9 | ~spl6_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f148,f138,f106,f101,f159])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    spl6_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl6_9 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    spl6_17 <=> ! [X1,X0,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_8 | ~spl6_9 | ~spl6_17)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f103,f107,f139])).
% 0.20/0.47  fof(f139,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) ) | ~spl6_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f138])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl6_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl6_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f101])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    spl6_17),
% 0.20/0.47    inference(avatar_split_clause,[],[f62,f138])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.47  % (28579)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    spl6_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f59,f126])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl6_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f57,f122])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    spl6_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f54,f110])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl6_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f46,f106])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl6_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f101])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ~spl6_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f96])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f25,f24])).
% 0.20/0.48  % (28576)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (28580)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (28594)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.48    inference(negated_conjecture,[],[f11])).
% 0.20/0.48  fof(f11,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl6_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f43,f91])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    l1_waybel_0(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ~spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f76])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ~v2_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl6_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f71])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    l1_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ~spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f66])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (28581)------------------------------
% 0.20/0.48  % (28581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (28581)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (28581)Memory used [KB]: 6268
% 0.20/0.48  % (28581)Time elapsed: 0.039 s
% 0.20/0.48  % (28581)------------------------------
% 0.20/0.48  % (28581)------------------------------
% 0.20/0.48  % (28573)Success in time 0.119 s
%------------------------------------------------------------------------------
