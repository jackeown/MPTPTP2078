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
% DateTime   : Thu Dec  3 13:22:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 615 expanded)
%              Number of leaves         :   37 ( 262 expanded)
%              Depth                    :   12
%              Number of atoms          :  907 (5447 expanded)
%              Number of equality atoms :   51 ( 340 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1854,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f97,f101,f105,f109,f264,f282,f315,f324,f333,f337,f574,f577,f588,f685,f695,f700,f971,f1448,f1503,f1510,f1564,f1565,f1566,f1567,f1644,f1837,f1852,f1853])).

fof(f1853,plain,
    ( ~ spl8_27
    | ~ spl8_11
    | spl8_9
    | ~ spl8_14
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f1595,f256,f146,f103,f135,f211])).

fof(f211,plain,
    ( spl8_27
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f135,plain,
    ( spl8_11
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f103,plain,
    ( spl8_9
  <=> ! [X4] :
        ( v4_orders_2(k1_funct_1(sK2,X4))
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f146,plain,
    ( spl8_14
  <=> ! [X3] :
        ( v4_orders_2(X3)
        | ~ r2_hidden(X3,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f256,plain,
    ( spl8_33
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f1595,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | v4_orders_2(k1_funct_1(sK2,X0))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_14
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f1588,f258])).

fof(f258,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f256])).

fof(f1588,plain,
    ( ! [X0] :
        ( v4_orders_2(k1_funct_1(sK2,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_14 ),
    inference(resolution,[],[f147,f64])).

fof(f64,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK5(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1),X1) )
              & ( ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
                  & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                    & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK5(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f147,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | v4_orders_2(X3) )
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f1852,plain,
    ( ~ spl8_27
    | ~ spl8_11
    | spl8_8
    | ~ spl8_15
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f1609,f256,f150,f99,f135,f211])).

fof(f99,plain,
    ( spl8_8
  <=> ! [X4] :
        ( v7_waybel_0(k1_funct_1(sK2,X4))
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f150,plain,
    ( spl8_15
  <=> ! [X6] :
        ( v7_waybel_0(X6)
        | ~ r2_hidden(X6,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f1609,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | v7_waybel_0(k1_funct_1(sK2,X0))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_15
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f1602,f258])).

fof(f1602,plain,
    ( ! [X0] :
        ( v7_waybel_0(k1_funct_1(sK2,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_15 ),
    inference(resolution,[],[f151,f64])).

fof(f151,plain,
    ( ! [X6] :
        ( ~ r2_hidden(X6,k2_relat_1(sK2))
        | v7_waybel_0(X6) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f150])).

fof(f1837,plain,
    ( ~ spl8_27
    | ~ spl8_11
    | ~ spl8_6
    | ~ spl8_2
    | ~ spl8_13
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f1836,f256,f142,f73,f90,f135,f211])).

fof(f90,plain,
    ( spl8_6
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f73,plain,
    ( spl8_2
  <=> v2_struct_0(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f142,plain,
    ( spl8_13
  <=> ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f1836,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_2
    | ~ spl8_13
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f1831,f258])).

fof(f1831,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(resolution,[],[f1664,f64])).

fof(f1664,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(resolution,[],[f75,f143])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f75,plain,
    ( v2_struct_0(k1_funct_1(sK2,sK3))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f1644,plain,
    ( ~ spl8_27
    | ~ spl8_11
    | spl8_7
    | ~ spl8_33
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f1643,f569,f256,f95,f135,f211])).

fof(f95,plain,
    ( spl8_7
  <=> ! [X4] :
        ( l1_waybel_0(k1_funct_1(sK2,X4),sK1)
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f569,plain,
    ( spl8_66
  <=> ! [X3] :
        ( l1_waybel_0(X3,sK1)
        | ~ r2_hidden(X3,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f1643,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | l1_waybel_0(k1_funct_1(sK2,X0),sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_33
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f1635,f258])).

fof(f1635,plain,
    ( ! [X0] :
        ( l1_waybel_0(k1_funct_1(sK2,X0),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_66 ),
    inference(resolution,[],[f570,f64])).

fof(f570,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK2))
        | l1_waybel_0(X3,sK1) )
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f569])).

fof(f1567,plain,
    ( ~ spl8_35
    | ~ spl8_27
    | ~ spl8_34
    | ~ spl8_11
    | ~ spl8_28
    | spl8_13
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f1487,f69,f142,f234,f135,f273,f211,f286])).

fof(f286,plain,
    ( spl8_35
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f273,plain,
    ( spl8_34
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f234,plain,
    ( spl8_28
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f69,plain,
    ( spl8_1
  <=> m3_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1487,plain,
    ( ! [X0] :
        ( ~ v2_struct_0(X0)
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_partfun1(sK2,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v4_relat_1(sK2,sK0)
        | ~ v1_relat_1(sK2)
        | ~ l1_struct_0(sK1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f70,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v2_struct_0(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( m3_yellow_6(X2,X0,X1)
              | ( ( ~ l1_waybel_0(sK4(X1,X2),X1)
                  | ~ v7_waybel_0(sK4(X1,X2))
                  | ~ v4_orders_2(sK4(X1,X2))
                  | v2_struct_0(sK4(X1,X2)) )
                & r2_hidden(sK4(X1,X2),k2_relat_1(X2)) ) )
            & ( ! [X4] :
                  ( ( l1_waybel_0(X4,X1)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X4,k2_relat_1(X2)) )
              | ~ m3_yellow_6(X2,X0,X1) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ( ~ l1_waybel_0(X3,X1)
            | ~ v7_waybel_0(X3)
            | ~ v4_orders_2(X3)
            | v2_struct_0(X3) )
          & r2_hidden(X3,k2_relat_1(X2)) )
     => ( ( ~ l1_waybel_0(sK4(X1,X2),X1)
          | ~ v7_waybel_0(sK4(X1,X2))
          | ~ v4_orders_2(sK4(X1,X2))
          | v2_struct_0(sK4(X1,X2)) )
        & r2_hidden(sK4(X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( m3_yellow_6(X2,X0,X1)
              | ? [X3] :
                  ( ( ~ l1_waybel_0(X3,X1)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                  & r2_hidden(X3,k2_relat_1(X2)) ) )
            & ( ! [X4] :
                  ( ( l1_waybel_0(X4,X1)
                    & v7_waybel_0(X4)
                    & v4_orders_2(X4)
                    & ~ v2_struct_0(X4) )
                  | ~ r2_hidden(X4,k2_relat_1(X2)) )
              | ~ m3_yellow_6(X2,X0,X1) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( m3_yellow_6(X2,X0,X1)
              | ? [X3] :
                  ( ( ~ l1_waybel_0(X3,X1)
                    | ~ v7_waybel_0(X3)
                    | ~ v4_orders_2(X3)
                    | v2_struct_0(X3) )
                  & r2_hidden(X3,k2_relat_1(X2)) ) )
            & ( ! [X3] :
                  ( ( l1_waybel_0(X3,X1)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) )
                  | ~ r2_hidden(X3,k2_relat_1(X2)) )
              | ~ m3_yellow_6(X2,X0,X1) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) )
                | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) )
                | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k2_relat_1(X2))
               => ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_yellow_6)).

fof(f70,plain,
    ( m3_yellow_6(sK2,sK0,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f1566,plain,
    ( ~ spl8_35
    | ~ spl8_27
    | ~ spl8_34
    | ~ spl8_11
    | ~ spl8_28
    | spl8_14
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f1488,f69,f146,f234,f135,f273,f211,f286])).

fof(f1488,plain,
    ( ! [X1] :
        ( v4_orders_2(X1)
        | ~ r2_hidden(X1,k2_relat_1(sK2))
        | ~ v1_partfun1(sK2,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v4_relat_1(sK2,sK0)
        | ~ v1_relat_1(sK2)
        | ~ l1_struct_0(sK1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( v4_orders_2(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1565,plain,
    ( ~ spl8_35
    | ~ spl8_27
    | ~ spl8_34
    | ~ spl8_11
    | ~ spl8_28
    | spl8_15
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f1489,f69,f150,f234,f135,f273,f211,f286])).

fof(f1489,plain,
    ( ! [X2] :
        ( v7_waybel_0(X2)
        | ~ r2_hidden(X2,k2_relat_1(sK2))
        | ~ v1_partfun1(sK2,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v4_relat_1(sK2,sK0)
        | ~ v1_relat_1(sK2)
        | ~ l1_struct_0(sK1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( v7_waybel_0(X4)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1564,plain,
    ( ~ spl8_35
    | ~ spl8_27
    | ~ spl8_34
    | ~ spl8_11
    | ~ spl8_28
    | spl8_66
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f1490,f69,f569,f234,f135,f273,f211,f286])).

fof(f1490,plain,
    ( ! [X3] :
        ( l1_waybel_0(X3,sK1)
        | ~ r2_hidden(X3,k2_relat_1(sK2))
        | ~ v1_partfun1(sK2,sK0)
        | ~ v1_funct_1(sK2)
        | ~ v4_relat_1(sK2,sK0)
        | ~ v1_relat_1(sK2)
        | ~ l1_struct_0(sK1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( l1_waybel_0(X4,X1)
      | ~ r2_hidden(X4,k2_relat_1(X2))
      | ~ m3_yellow_6(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1510,plain,
    ( spl8_3
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f1508])).

fof(f1508,plain,
    ( $false
    | spl8_3
    | ~ spl8_6
    | ~ spl8_9 ),
    inference(unit_resulting_resolution,[],[f92,f79,f104])).

fof(f104,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | v4_orders_2(k1_funct_1(sK2,X4)) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f79,plain,
    ( ~ v4_orders_2(k1_funct_1(sK2,sK3))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_3
  <=> v4_orders_2(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f92,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f1503,plain,
    ( spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f1501])).

fof(f1501,plain,
    ( $false
    | spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f92,f87,f96])).

fof(f96,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | l1_waybel_0(k1_funct_1(sK2,X4),sK1) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f87,plain,
    ( ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_5
  <=> l1_waybel_0(k1_funct_1(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f1448,plain,
    ( spl8_1
    | ~ spl8_7
    | spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(avatar_contradiction_clause,[],[f1440])).

% (28108)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f1440,plain,
    ( $false
    | spl8_1
    | ~ spl8_7
    | spl8_37
    | ~ spl8_38
    | ~ spl8_39
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(unit_resulting_resolution,[],[f34,f35,f37,f36,f38,f71,f296,f300,f304,f1435,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m3_yellow_6(X2,X0,X1)
      | ~ l1_waybel_0(sK4(X1,X2),X1)
      | ~ v7_waybel_0(sK4(X1,X2))
      | ~ v4_orders_2(sK4(X1,X2))
      | v2_struct_0(sK4(X1,X2))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1435,plain,
    ( l1_waybel_0(sK4(sK1,sK2),sK1)
    | ~ spl8_7
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(forward_demodulation,[],[f615,f527])).

fof(f527,plain,
    ( sK4(sK1,sK2) = k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2)))
    | ~ spl8_61 ),
    inference(avatar_component_clause,[],[f525])).

fof(f525,plain,
    ( spl8_61
  <=> sK4(sK1,sK2) = k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f615,plain,
    ( l1_waybel_0(k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2))),sK1)
    | ~ spl8_7
    | ~ spl8_60 ),
    inference(resolution,[],[f522,f96])).

fof(f522,plain,
    ( r2_hidden(sK7(sK2,sK4(sK1,sK2)),sK0)
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f520])).

fof(f520,plain,
    ( spl8_60
  <=> r2_hidden(sK7(sK2,sK4(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f304,plain,
    ( v7_waybel_0(sK4(sK1,sK2))
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl8_39
  <=> v7_waybel_0(sK4(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f300,plain,
    ( v4_orders_2(sK4(sK1,sK2))
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl8_38
  <=> v4_orders_2(sK4(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f296,plain,
    ( ~ v2_struct_0(sK4(sK1,sK2))
    | spl8_37 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl8_37
  <=> v2_struct_0(sK4(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f71,plain,
    ( ~ m3_yellow_6(sK2,sK0,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f38,plain,(
    v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( ( ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
          | ~ v7_waybel_0(k1_funct_1(sK2,sK3))
          | ~ v4_orders_2(k1_funct_1(sK2,sK3))
          | v2_struct_0(k1_funct_1(sK2,sK3)) )
        & r2_hidden(sK3,sK0) )
      | ~ m3_yellow_6(sK2,sK0,sK1) )
    & ( ! [X4] :
          ( ( l1_waybel_0(k1_funct_1(sK2,X4),sK1)
            & v7_waybel_0(k1_funct_1(sK2,X4))
            & v4_orders_2(k1_funct_1(sK2,X4))
            & ~ v2_struct_0(k1_funct_1(sK2,X4)) )
          | ~ r2_hidden(X4,sK0) )
      | m3_yellow_6(sK2,sK0,sK1) )
    & v1_partfun1(sK2,sK0)
    & v1_funct_1(sK2)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21,f20,f19])).

% (28107)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ? [X3] :
                  ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                    | ~ v7_waybel_0(k1_funct_1(X2,X3))
                    | ~ v4_orders_2(k1_funct_1(X2,X3))
                    | v2_struct_0(k1_funct_1(X2,X3)) )
                  & r2_hidden(X3,X0) )
              | ~ m3_yellow_6(X2,X0,X1) )
            & ( ! [X4] :
                  ( ( l1_waybel_0(k1_funct_1(X2,X4),X1)
                    & v7_waybel_0(k1_funct_1(X2,X4))
                    & v4_orders_2(k1_funct_1(X2,X4))
                    & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                  | ~ r2_hidden(X4,X0) )
              | m3_yellow_6(X2,X0,X1) )
            & v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),sK1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,sK0) )
            | ~ m3_yellow_6(X2,sK0,sK1) )
          & ( ! [X4] :
                ( ( l1_waybel_0(k1_funct_1(X2,X4),sK1)
                  & v7_waybel_0(k1_funct_1(X2,X4))
                  & v4_orders_2(k1_funct_1(X2,X4))
                  & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                | ~ r2_hidden(X4,sK0) )
            | m3_yellow_6(X2,sK0,sK1) )
          & v1_partfun1(X2,sK0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( ? [X3] :
              ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),sK1)
                | ~ v7_waybel_0(k1_funct_1(X2,X3))
                | ~ v4_orders_2(k1_funct_1(X2,X3))
                | v2_struct_0(k1_funct_1(X2,X3)) )
              & r2_hidden(X3,sK0) )
          | ~ m3_yellow_6(X2,sK0,sK1) )
        & ( ! [X4] :
              ( ( l1_waybel_0(k1_funct_1(X2,X4),sK1)
                & v7_waybel_0(k1_funct_1(X2,X4))
                & v4_orders_2(k1_funct_1(X2,X4))
                & ~ v2_struct_0(k1_funct_1(X2,X4)) )
              | ~ r2_hidden(X4,sK0) )
          | m3_yellow_6(X2,sK0,sK1) )
        & v1_partfun1(X2,sK0)
        & v1_funct_1(X2)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ( ? [X3] :
            ( ( ~ l1_waybel_0(k1_funct_1(sK2,X3),sK1)
              | ~ v7_waybel_0(k1_funct_1(sK2,X3))
              | ~ v4_orders_2(k1_funct_1(sK2,X3))
              | v2_struct_0(k1_funct_1(sK2,X3)) )
            & r2_hidden(X3,sK0) )
        | ~ m3_yellow_6(sK2,sK0,sK1) )
      & ( ! [X4] :
            ( ( l1_waybel_0(k1_funct_1(sK2,X4),sK1)
              & v7_waybel_0(k1_funct_1(sK2,X4))
              & v4_orders_2(k1_funct_1(sK2,X4))
              & ~ v2_struct_0(k1_funct_1(sK2,X4)) )
            | ~ r2_hidden(X4,sK0) )
        | m3_yellow_6(sK2,sK0,sK1) )
      & v1_partfun1(sK2,sK0)
      & v1_funct_1(sK2)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3] :
        ( ( ~ l1_waybel_0(k1_funct_1(sK2,X3),sK1)
          | ~ v7_waybel_0(k1_funct_1(sK2,X3))
          | ~ v4_orders_2(k1_funct_1(sK2,X3))
          | v2_struct_0(k1_funct_1(sK2,X3)) )
        & r2_hidden(X3,sK0) )
   => ( ( ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
        | ~ v7_waybel_0(k1_funct_1(sK2,sK3))
        | ~ v4_orders_2(k1_funct_1(sK2,sK3))
        | v2_struct_0(k1_funct_1(sK2,sK3)) )
      & r2_hidden(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X4] :
                ( ( l1_waybel_0(k1_funct_1(X2,X4),X1)
                  & v7_waybel_0(k1_funct_1(X2,X4))
                  & v4_orders_2(k1_funct_1(X2,X4))
                  & ~ v2_struct_0(k1_funct_1(X2,X4)) )
                | ~ r2_hidden(X4,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ l1_waybel_0(k1_funct_1(X2,X3),X1)
                  | ~ v7_waybel_0(k1_funct_1(X2,X3))
                  | ~ v4_orders_2(k1_funct_1(X2,X3))
                  | v2_struct_0(k1_funct_1(X2,X3)) )
                & r2_hidden(X3,X0) )
            | ~ m3_yellow_6(X2,X0,X1) )
          & ( ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) )
            | m3_yellow_6(X2,X0,X1) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <~> ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) ) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <~> ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) ) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( v1_partfun1(X2,X0)
              & v1_funct_1(X2)
              & v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( m3_yellow_6(X2,X0,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                    & v7_waybel_0(k1_funct_1(X2,X3))
                    & v4_orders_2(k1_funct_1(X2,X3))
                    & ~ v2_struct_0(k1_funct_1(X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

% (28110)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% (28110)Refutation not found, incomplete strategy% (28110)------------------------------
% (28110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28110)Termination reason: Refutation not found, incomplete strategy

% (28110)Memory used [KB]: 10618
% (28110)Time elapsed: 0.114 s
% (28110)------------------------------
% (28110)------------------------------
% (28109)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f5,conjecture,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,X0)
               => ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_yellow_6)).

fof(f36,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f971,plain,
    ( ~ spl8_27
    | ~ spl8_11
    | spl8_61
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f962,f290,f525,f135,f211])).

fof(f290,plain,
    ( spl8_36
  <=> r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f962,plain,
    ( sK4(sK1,sK2) = k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_36 ),
    inference(resolution,[],[f292,f65])).

fof(f65,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK7(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK7(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f292,plain,
    ( r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f290])).

fof(f700,plain,
    ( ~ spl8_27
    | ~ spl8_11
    | ~ spl8_36
    | ~ spl8_37
    | ~ spl8_10
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f681,f520,f107,f295,f290,f135,f211])).

fof(f107,plain,
    ( spl8_10
  <=> ! [X4] :
        ( ~ v2_struct_0(k1_funct_1(sK2,X4))
        | ~ r2_hidden(X4,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f681,plain,
    ( ~ v2_struct_0(sK4(sK1,sK2))
    | ~ r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_10
    | ~ spl8_60 ),
    inference(superposition,[],[f616,f65])).

fof(f616,plain,
    ( ~ v2_struct_0(k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2))))
    | ~ spl8_10
    | ~ spl8_60 ),
    inference(resolution,[],[f522,f108])).

fof(f108,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | ~ v2_struct_0(k1_funct_1(sK2,X4)) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f695,plain,
    ( ~ spl8_27
    | ~ spl8_11
    | ~ spl8_36
    | spl8_39
    | ~ spl8_8
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f694,f520,f99,f303,f290,f135,f211])).

fof(f694,plain,
    ( v7_waybel_0(sK4(sK1,sK2))
    | ~ r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_8
    | ~ spl8_60 ),
    inference(superposition,[],[f618,f65])).

fof(f618,plain,
    ( v7_waybel_0(k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2))))
    | ~ spl8_8
    | ~ spl8_60 ),
    inference(resolution,[],[f522,f100])).

fof(f100,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | v7_waybel_0(k1_funct_1(sK2,X4)) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f685,plain,
    ( ~ spl8_27
    | ~ spl8_11
    | ~ spl8_36
    | spl8_38
    | ~ spl8_9
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f684,f520,f103,f299,f290,f135,f211])).

fof(f684,plain,
    ( v4_orders_2(sK4(sK1,sK2))
    | ~ r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_9
    | ~ spl8_60 ),
    inference(superposition,[],[f617,f65])).

fof(f617,plain,
    ( v4_orders_2(k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2))))
    | ~ spl8_9
    | ~ spl8_60 ),
    inference(resolution,[],[f522,f104])).

fof(f588,plain,
    ( ~ spl8_27
    | ~ spl8_11
    | spl8_60
    | ~ spl8_33
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f587,f290,f256,f520,f135,f211])).

fof(f587,plain,
    ( r2_hidden(sK7(sK2,sK4(sK1,sK2)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_33
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f578,f258])).

fof(f578,plain,
    ( r2_hidden(sK7(sK2,sK4(sK1,sK2)),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_36 ),
    inference(resolution,[],[f292,f66])).

fof(f66,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK7(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f577,plain,
    ( spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | spl8_4
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f92,f83,f100])).

fof(f83,plain,
    ( ~ v7_waybel_0(k1_funct_1(sK2,sK3))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl8_4
  <=> v7_waybel_0(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f574,plain,
    ( ~ spl8_35
    | ~ spl8_27
    | ~ spl8_34
    | ~ spl8_11
    | ~ spl8_28
    | spl8_36
    | spl8_1 ),
    inference(avatar_split_clause,[],[f572,f69,f290,f234,f135,f273,f211,f286])).

fof(f572,plain,
    ( r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | ~ v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ l1_struct_0(sK1)
    | spl8_1 ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m3_yellow_6(X2,X0,X1)
      | r2_hidden(sK4(X1,X2),k2_relat_1(X2))
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f337,plain,(
    spl8_35 ),
    inference(avatar_contradiction_clause,[],[f334])).

fof(f334,plain,
    ( $false
    | spl8_35 ),
    inference(unit_resulting_resolution,[],[f34,f288])).

fof(f288,plain,
    ( ~ l1_struct_0(sK1)
    | spl8_35 ),
    inference(avatar_component_clause,[],[f286])).

fof(f333,plain,(
    spl8_34 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | spl8_34 ),
    inference(unit_resulting_resolution,[],[f36,f275])).

fof(f275,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl8_34 ),
    inference(avatar_component_clause,[],[f273])).

fof(f324,plain,(
    spl8_28 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl8_28 ),
    inference(unit_resulting_resolution,[],[f38,f236])).

fof(f236,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f234])).

fof(f315,plain,(
    spl8_27 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl8_27 ),
    inference(unit_resulting_resolution,[],[f35,f213])).

fof(f213,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f211])).

fof(f282,plain,
    ( ~ spl8_27
    | ~ spl8_34
    | spl8_33 ),
    inference(avatar_split_clause,[],[f271,f256,f273,f211])).

fof(f271,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f38,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f264,plain,(
    spl8_11 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl8_11 ),
    inference(unit_resulting_resolution,[],[f37,f137])).

fof(f137,plain,
    ( ~ v1_funct_1(sK2)
    | spl8_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f109,plain,
    ( spl8_1
    | spl8_10 ),
    inference(avatar_split_clause,[],[f39,f107,f69])).

fof(f39,plain,(
    ! [X4] :
      ( ~ v2_struct_0(k1_funct_1(sK2,X4))
      | ~ r2_hidden(X4,sK0)
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,
    ( spl8_1
    | spl8_9 ),
    inference(avatar_split_clause,[],[f40,f103,f69])).

fof(f40,plain,(
    ! [X4] :
      ( v4_orders_2(k1_funct_1(sK2,X4))
      | ~ r2_hidden(X4,sK0)
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,
    ( spl8_1
    | spl8_8 ),
    inference(avatar_split_clause,[],[f41,f99,f69])).

fof(f41,plain,(
    ! [X4] :
      ( v7_waybel_0(k1_funct_1(sK2,X4))
      | ~ r2_hidden(X4,sK0)
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,
    ( spl8_1
    | spl8_7 ),
    inference(avatar_split_clause,[],[f42,f95,f69])).

fof(f42,plain,(
    ! [X4] :
      ( l1_waybel_0(k1_funct_1(sK2,X4),sK1)
      | ~ r2_hidden(X4,sK0)
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,
    ( ~ spl8_1
    | spl8_6 ),
    inference(avatar_split_clause,[],[f43,f90,f69])).

fof(f43,plain,
    ( r2_hidden(sK3,sK0)
    | ~ m3_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,
    ( ~ spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f44,f85,f81,f77,f73,f69])).

fof(f44,plain,
    ( ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
    | ~ v7_waybel_0(k1_funct_1(sK2,sK3))
    | ~ v4_orders_2(k1_funct_1(sK2,sK3))
    | v2_struct_0(k1_funct_1(sK2,sK3))
    | ~ m3_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (28098)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (28100)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (28091)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (28105)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (28091)Refutation not found, incomplete strategy% (28091)------------------------------
% 0.21/0.48  % (28091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28091)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28091)Memory used [KB]: 10618
% 0.21/0.49  % (28091)Time elapsed: 0.061 s
% 0.21/0.49  % (28091)------------------------------
% 0.21/0.49  % (28091)------------------------------
% 0.21/0.50  % (28104)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (28102)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (28094)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (28092)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (28095)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (28090)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (28097)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (28106)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (28099)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (28096)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (28103)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (28093)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (28100)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1854,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f88,f93,f97,f101,f105,f109,f264,f282,f315,f324,f333,f337,f574,f577,f588,f685,f695,f700,f971,f1448,f1503,f1510,f1564,f1565,f1566,f1567,f1644,f1837,f1852,f1853])).
% 0.21/0.52  fof(f1853,plain,(
% 0.21/0.52    ~spl8_27 | ~spl8_11 | spl8_9 | ~spl8_14 | ~spl8_33),
% 0.21/0.52    inference(avatar_split_clause,[],[f1595,f256,f146,f103,f135,f211])).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    spl8_27 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    spl8_11 <=> v1_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl8_9 <=> ! [X4] : (v4_orders_2(k1_funct_1(sK2,X4)) | ~r2_hidden(X4,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl8_14 <=> ! [X3] : (v4_orders_2(X3) | ~r2_hidden(X3,k2_relat_1(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    spl8_33 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 0.21/0.52  fof(f1595,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | v4_orders_2(k1_funct_1(sK2,X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl8_14 | ~spl8_33)),
% 0.21/0.52    inference(forward_demodulation,[],[f1588,f258])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK2) | ~spl8_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f256])).
% 0.21/0.52  fof(f1588,plain,(
% 0.21/0.52    ( ! [X0] : (v4_orders_2(k1_funct_1(sK2,X0)) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_14),
% 0.21/0.52    inference(resolution,[],[f147,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & ((sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f28,f31,f30,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(rectify,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | v4_orders_2(X3)) ) | ~spl8_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f146])).
% 0.21/0.52  fof(f1852,plain,(
% 0.21/0.52    ~spl8_27 | ~spl8_11 | spl8_8 | ~spl8_15 | ~spl8_33),
% 0.21/0.52    inference(avatar_split_clause,[],[f1609,f256,f150,f99,f135,f211])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl8_8 <=> ! [X4] : (v7_waybel_0(k1_funct_1(sK2,X4)) | ~r2_hidden(X4,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl8_15 <=> ! [X6] : (v7_waybel_0(X6) | ~r2_hidden(X6,k2_relat_1(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.52  fof(f1609,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | v7_waybel_0(k1_funct_1(sK2,X0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl8_15 | ~spl8_33)),
% 0.21/0.52    inference(forward_demodulation,[],[f1602,f258])).
% 0.21/0.52  fof(f1602,plain,(
% 0.21/0.52    ( ! [X0] : (v7_waybel_0(k1_funct_1(sK2,X0)) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_15),
% 0.21/0.52    inference(resolution,[],[f151,f64])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ( ! [X6] : (~r2_hidden(X6,k2_relat_1(sK2)) | v7_waybel_0(X6)) ) | ~spl8_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f150])).
% 0.21/0.52  fof(f1837,plain,(
% 0.21/0.52    ~spl8_27 | ~spl8_11 | ~spl8_6 | ~spl8_2 | ~spl8_13 | ~spl8_33),
% 0.21/0.52    inference(avatar_split_clause,[],[f1836,f256,f142,f73,f90,f135,f211])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl8_6 <=> r2_hidden(sK3,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl8_2 <=> v2_struct_0(k1_funct_1(sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl8_13 <=> ! [X0] : (~v2_struct_0(X0) | ~r2_hidden(X0,k2_relat_1(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.52  fof(f1836,plain,(
% 0.21/0.52    ~r2_hidden(sK3,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_2 | ~spl8_13 | ~spl8_33)),
% 0.21/0.52    inference(forward_demodulation,[],[f1831,f258])).
% 0.21/0.52  fof(f1831,plain,(
% 0.21/0.52    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_2 | ~spl8_13)),
% 0.21/0.52    inference(resolution,[],[f1664,f64])).
% 0.21/0.52  fof(f1664,plain,(
% 0.21/0.52    ~r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2)) | (~spl8_2 | ~spl8_13)),
% 0.21/0.52    inference(resolution,[],[f75,f143])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_struct_0(X0) | ~r2_hidden(X0,k2_relat_1(sK2))) ) | ~spl8_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f142])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    v2_struct_0(k1_funct_1(sK2,sK3)) | ~spl8_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f1644,plain,(
% 0.21/0.52    ~spl8_27 | ~spl8_11 | spl8_7 | ~spl8_33 | ~spl8_66),
% 0.21/0.52    inference(avatar_split_clause,[],[f1643,f569,f256,f95,f135,f211])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl8_7 <=> ! [X4] : (l1_waybel_0(k1_funct_1(sK2,X4),sK1) | ~r2_hidden(X4,sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.52  fof(f569,plain,(
% 0.21/0.52    spl8_66 <=> ! [X3] : (l1_waybel_0(X3,sK1) | ~r2_hidden(X3,k2_relat_1(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).
% 0.21/0.52  fof(f1643,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | l1_waybel_0(k1_funct_1(sK2,X0),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl8_33 | ~spl8_66)),
% 0.21/0.52    inference(forward_demodulation,[],[f1635,f258])).
% 0.21/0.52  fof(f1635,plain,(
% 0.21/0.52    ( ! [X0] : (l1_waybel_0(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_66),
% 0.21/0.52    inference(resolution,[],[f570,f64])).
% 0.21/0.52  fof(f570,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | l1_waybel_0(X3,sK1)) ) | ~spl8_66),
% 0.21/0.52    inference(avatar_component_clause,[],[f569])).
% 0.21/0.52  fof(f1567,plain,(
% 0.21/0.52    ~spl8_35 | ~spl8_27 | ~spl8_34 | ~spl8_11 | ~spl8_28 | spl8_13 | ~spl8_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f1487,f69,f142,f234,f135,f273,f211,f286])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    spl8_35 <=> l1_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    spl8_34 <=> v4_relat_1(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    spl8_28 <=> v1_partfun1(sK2,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl8_1 <=> m3_yellow_6(sK2,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.52  fof(f1487,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_struct_0(X0) | ~r2_hidden(X0,k2_relat_1(sK2)) | ~v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~l1_struct_0(sK1)) ) | ~spl8_1),
% 0.21/0.52    inference(resolution,[],[f70,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~v2_struct_0(X4) | ~r2_hidden(X4,k2_relat_1(X2)) | ~m3_yellow_6(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~l1_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (((m3_yellow_6(X2,X0,X1) | ((~l1_waybel_0(sK4(X1,X2),X1) | ~v7_waybel_0(sK4(X1,X2)) | ~v4_orders_2(sK4(X1,X2)) | v2_struct_0(sK4(X1,X2))) & r2_hidden(sK4(X1,X2),k2_relat_1(X2)))) & (! [X4] : ((l1_waybel_0(X4,X1) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) | ~r2_hidden(X4,k2_relat_1(X2))) | ~m3_yellow_6(X2,X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~l1_struct_0(X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X2,X1] : (? [X3] : ((~l1_waybel_0(X3,X1) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) & r2_hidden(X3,k2_relat_1(X2))) => ((~l1_waybel_0(sK4(X1,X2),X1) | ~v7_waybel_0(sK4(X1,X2)) | ~v4_orders_2(sK4(X1,X2)) | v2_struct_0(sK4(X1,X2))) & r2_hidden(sK4(X1,X2),k2_relat_1(X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (((m3_yellow_6(X2,X0,X1) | ? [X3] : ((~l1_waybel_0(X3,X1) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) & r2_hidden(X3,k2_relat_1(X2)))) & (! [X4] : ((l1_waybel_0(X4,X1) & v7_waybel_0(X4) & v4_orders_2(X4) & ~v2_struct_0(X4)) | ~r2_hidden(X4,k2_relat_1(X2))) | ~m3_yellow_6(X2,X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~l1_struct_0(X1))),
% 0.21/0.52    inference(rectify,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (((m3_yellow_6(X2,X0,X1) | ? [X3] : ((~l1_waybel_0(X3,X1) | ~v7_waybel_0(X3) | ~v4_orders_2(X3) | v2_struct_0(X3)) & r2_hidden(X3,k2_relat_1(X2)))) & (! [X3] : ((l1_waybel_0(X3,X1) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~r2_hidden(X3,k2_relat_1(X2))) | ~m3_yellow_6(X2,X0,X1))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~l1_struct_0(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((m3_yellow_6(X2,X0,X1) <=> ! [X3] : ((l1_waybel_0(X3,X1) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~r2_hidden(X3,k2_relat_1(X2)))) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~l1_struct_0(X1))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((m3_yellow_6(X2,X0,X1) <=> ! [X3] : ((l1_waybel_0(X3,X1) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3)) | ~r2_hidden(X3,k2_relat_1(X2)))) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~l1_struct_0(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (l1_struct_0(X1) => ! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) => (m3_yellow_6(X2,X0,X1) <=> ! [X3] : (r2_hidden(X3,k2_relat_1(X2)) => (l1_waybel_0(X3,X1) & v7_waybel_0(X3) & v4_orders_2(X3) & ~v2_struct_0(X3))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_yellow_6)).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    m3_yellow_6(sK2,sK0,sK1) | ~spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f1566,plain,(
% 0.21/0.52    ~spl8_35 | ~spl8_27 | ~spl8_34 | ~spl8_11 | ~spl8_28 | spl8_14 | ~spl8_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f1488,f69,f146,f234,f135,f273,f211,f286])).
% 0.21/0.52  fof(f1488,plain,(
% 0.21/0.52    ( ! [X1] : (v4_orders_2(X1) | ~r2_hidden(X1,k2_relat_1(sK2)) | ~v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~l1_struct_0(sK1)) ) | ~spl8_1),
% 0.21/0.52    inference(resolution,[],[f70,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (v4_orders_2(X4) | ~r2_hidden(X4,k2_relat_1(X2)) | ~m3_yellow_6(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~l1_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f1565,plain,(
% 0.21/0.52    ~spl8_35 | ~spl8_27 | ~spl8_34 | ~spl8_11 | ~spl8_28 | spl8_15 | ~spl8_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f1489,f69,f150,f234,f135,f273,f211,f286])).
% 0.21/0.52  fof(f1489,plain,(
% 0.21/0.52    ( ! [X2] : (v7_waybel_0(X2) | ~r2_hidden(X2,k2_relat_1(sK2)) | ~v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~l1_struct_0(sK1)) ) | ~spl8_1),
% 0.21/0.52    inference(resolution,[],[f70,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (v7_waybel_0(X4) | ~r2_hidden(X4,k2_relat_1(X2)) | ~m3_yellow_6(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~l1_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f1564,plain,(
% 0.21/0.52    ~spl8_35 | ~spl8_27 | ~spl8_34 | ~spl8_11 | ~spl8_28 | spl8_66 | ~spl8_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f1490,f69,f569,f234,f135,f273,f211,f286])).
% 0.21/0.52  fof(f1490,plain,(
% 0.21/0.52    ( ! [X3] : (l1_waybel_0(X3,sK1) | ~r2_hidden(X3,k2_relat_1(sK2)) | ~v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~l1_struct_0(sK1)) ) | ~spl8_1),
% 0.21/0.52    inference(resolution,[],[f70,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (l1_waybel_0(X4,X1) | ~r2_hidden(X4,k2_relat_1(X2)) | ~m3_yellow_6(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~l1_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f1510,plain,(
% 0.21/0.52    spl8_3 | ~spl8_6 | ~spl8_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1508])).
% 0.21/0.52  fof(f1508,plain,(
% 0.21/0.52    $false | (spl8_3 | ~spl8_6 | ~spl8_9)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f92,f79,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,sK0) | v4_orders_2(k1_funct_1(sK2,X4))) ) | ~spl8_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f103])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~v4_orders_2(k1_funct_1(sK2,sK3)) | spl8_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl8_3 <=> v4_orders_2(k1_funct_1(sK2,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    r2_hidden(sK3,sK0) | ~spl8_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f90])).
% 0.21/0.52  fof(f1503,plain,(
% 0.21/0.52    spl8_5 | ~spl8_6 | ~spl8_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1501])).
% 0.21/0.52  fof(f1501,plain,(
% 0.21/0.52    $false | (spl8_5 | ~spl8_6 | ~spl8_7)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f92,f87,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X4] : (~r2_hidden(X4,sK0) | l1_waybel_0(k1_funct_1(sK2,X4),sK1)) ) | ~spl8_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f95])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ~l1_waybel_0(k1_funct_1(sK2,sK3),sK1) | spl8_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl8_5 <=> l1_waybel_0(k1_funct_1(sK2,sK3),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.52  fof(f1448,plain,(
% 0.21/0.52    spl8_1 | ~spl8_7 | spl8_37 | ~spl8_38 | ~spl8_39 | ~spl8_60 | ~spl8_61),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1440])).
% 0.21/0.52  % (28108)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  fof(f1440,plain,(
% 0.21/0.52    $false | (spl8_1 | ~spl8_7 | spl8_37 | ~spl8_38 | ~spl8_39 | ~spl8_60 | ~spl8_61)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f34,f35,f37,f36,f38,f71,f296,f300,f304,f1435,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m3_yellow_6(X2,X0,X1) | ~l1_waybel_0(sK4(X1,X2),X1) | ~v7_waybel_0(sK4(X1,X2)) | ~v4_orders_2(sK4(X1,X2)) | v2_struct_0(sK4(X1,X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~l1_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f1435,plain,(
% 0.21/0.52    l1_waybel_0(sK4(sK1,sK2),sK1) | (~spl8_7 | ~spl8_60 | ~spl8_61)),
% 0.21/0.52    inference(forward_demodulation,[],[f615,f527])).
% 0.21/0.52  fof(f527,plain,(
% 0.21/0.52    sK4(sK1,sK2) = k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2))) | ~spl8_61),
% 0.21/0.52    inference(avatar_component_clause,[],[f525])).
% 0.21/0.52  fof(f525,plain,(
% 0.21/0.52    spl8_61 <=> sK4(sK1,sK2) = k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).
% 0.21/0.52  fof(f615,plain,(
% 0.21/0.52    l1_waybel_0(k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2))),sK1) | (~spl8_7 | ~spl8_60)),
% 0.21/0.52    inference(resolution,[],[f522,f96])).
% 0.21/0.52  fof(f522,plain,(
% 0.21/0.52    r2_hidden(sK7(sK2,sK4(sK1,sK2)),sK0) | ~spl8_60),
% 0.21/0.52    inference(avatar_component_clause,[],[f520])).
% 0.21/0.52  fof(f520,plain,(
% 0.21/0.52    spl8_60 <=> r2_hidden(sK7(sK2,sK4(sK1,sK2)),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    v7_waybel_0(sK4(sK1,sK2)) | ~spl8_39),
% 0.21/0.52    inference(avatar_component_clause,[],[f303])).
% 0.21/0.52  fof(f303,plain,(
% 0.21/0.52    spl8_39 <=> v7_waybel_0(sK4(sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.21/0.52  fof(f300,plain,(
% 0.21/0.52    v4_orders_2(sK4(sK1,sK2)) | ~spl8_38),
% 0.21/0.52    inference(avatar_component_clause,[],[f299])).
% 0.21/0.52  fof(f299,plain,(
% 0.21/0.52    spl8_38 <=> v4_orders_2(sK4(sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    ~v2_struct_0(sK4(sK1,sK2)) | spl8_37),
% 0.21/0.52    inference(avatar_component_clause,[],[f295])).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    spl8_37 <=> v2_struct_0(sK4(sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ~m3_yellow_6(sK2,sK0,sK1) | spl8_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    v1_partfun1(sK2,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ((((~l1_waybel_0(k1_funct_1(sK2,sK3),sK1) | ~v7_waybel_0(k1_funct_1(sK2,sK3)) | ~v4_orders_2(k1_funct_1(sK2,sK3)) | v2_struct_0(k1_funct_1(sK2,sK3))) & r2_hidden(sK3,sK0)) | ~m3_yellow_6(sK2,sK0,sK1)) & (! [X4] : ((l1_waybel_0(k1_funct_1(sK2,X4),sK1) & v7_waybel_0(k1_funct_1(sK2,X4)) & v4_orders_2(k1_funct_1(sK2,X4)) & ~v2_struct_0(k1_funct_1(sK2,X4))) | ~r2_hidden(X4,sK0)) | m3_yellow_6(sK2,sK0,sK1)) & v1_partfun1(sK2,sK0) & v1_funct_1(sK2) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2)) & l1_struct_0(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f21,f20,f19])).
% 0.21/0.52  % (28107)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((? [X3] : ((~l1_waybel_0(k1_funct_1(X2,X3),X1) | ~v7_waybel_0(k1_funct_1(X2,X3)) | ~v4_orders_2(k1_funct_1(X2,X3)) | v2_struct_0(k1_funct_1(X2,X3))) & r2_hidden(X3,X0)) | ~m3_yellow_6(X2,X0,X1)) & (! [X4] : ((l1_waybel_0(k1_funct_1(X2,X4),X1) & v7_waybel_0(k1_funct_1(X2,X4)) & v4_orders_2(k1_funct_1(X2,X4)) & ~v2_struct_0(k1_funct_1(X2,X4))) | ~r2_hidden(X4,X0)) | m3_yellow_6(X2,X0,X1)) & v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & l1_struct_0(X1)) => (? [X2] : ((? [X3] : ((~l1_waybel_0(k1_funct_1(X2,X3),sK1) | ~v7_waybel_0(k1_funct_1(X2,X3)) | ~v4_orders_2(k1_funct_1(X2,X3)) | v2_struct_0(k1_funct_1(X2,X3))) & r2_hidden(X3,sK0)) | ~m3_yellow_6(X2,sK0,sK1)) & (! [X4] : ((l1_waybel_0(k1_funct_1(X2,X4),sK1) & v7_waybel_0(k1_funct_1(X2,X4)) & v4_orders_2(k1_funct_1(X2,X4)) & ~v2_struct_0(k1_funct_1(X2,X4))) | ~r2_hidden(X4,sK0)) | m3_yellow_6(X2,sK0,sK1)) & v1_partfun1(X2,sK0) & v1_funct_1(X2) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) & l1_struct_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ? [X2] : ((? [X3] : ((~l1_waybel_0(k1_funct_1(X2,X3),sK1) | ~v7_waybel_0(k1_funct_1(X2,X3)) | ~v4_orders_2(k1_funct_1(X2,X3)) | v2_struct_0(k1_funct_1(X2,X3))) & r2_hidden(X3,sK0)) | ~m3_yellow_6(X2,sK0,sK1)) & (! [X4] : ((l1_waybel_0(k1_funct_1(X2,X4),sK1) & v7_waybel_0(k1_funct_1(X2,X4)) & v4_orders_2(k1_funct_1(X2,X4)) & ~v2_struct_0(k1_funct_1(X2,X4))) | ~r2_hidden(X4,sK0)) | m3_yellow_6(X2,sK0,sK1)) & v1_partfun1(X2,sK0) & v1_funct_1(X2) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) => ((? [X3] : ((~l1_waybel_0(k1_funct_1(sK2,X3),sK1) | ~v7_waybel_0(k1_funct_1(sK2,X3)) | ~v4_orders_2(k1_funct_1(sK2,X3)) | v2_struct_0(k1_funct_1(sK2,X3))) & r2_hidden(X3,sK0)) | ~m3_yellow_6(sK2,sK0,sK1)) & (! [X4] : ((l1_waybel_0(k1_funct_1(sK2,X4),sK1) & v7_waybel_0(k1_funct_1(sK2,X4)) & v4_orders_2(k1_funct_1(sK2,X4)) & ~v2_struct_0(k1_funct_1(sK2,X4))) | ~r2_hidden(X4,sK0)) | m3_yellow_6(sK2,sK0,sK1)) & v1_partfun1(sK2,sK0) & v1_funct_1(sK2) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X3] : ((~l1_waybel_0(k1_funct_1(sK2,X3),sK1) | ~v7_waybel_0(k1_funct_1(sK2,X3)) | ~v4_orders_2(k1_funct_1(sK2,X3)) | v2_struct_0(k1_funct_1(sK2,X3))) & r2_hidden(X3,sK0)) => ((~l1_waybel_0(k1_funct_1(sK2,sK3),sK1) | ~v7_waybel_0(k1_funct_1(sK2,sK3)) | ~v4_orders_2(k1_funct_1(sK2,sK3)) | v2_struct_0(k1_funct_1(sK2,sK3))) & r2_hidden(sK3,sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((? [X3] : ((~l1_waybel_0(k1_funct_1(X2,X3),X1) | ~v7_waybel_0(k1_funct_1(X2,X3)) | ~v4_orders_2(k1_funct_1(X2,X3)) | v2_struct_0(k1_funct_1(X2,X3))) & r2_hidden(X3,X0)) | ~m3_yellow_6(X2,X0,X1)) & (! [X4] : ((l1_waybel_0(k1_funct_1(X2,X4),X1) & v7_waybel_0(k1_funct_1(X2,X4)) & v4_orders_2(k1_funct_1(X2,X4)) & ~v2_struct_0(k1_funct_1(X2,X4))) | ~r2_hidden(X4,X0)) | m3_yellow_6(X2,X0,X1)) & v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & l1_struct_0(X1))),
% 0.21/0.52    inference(rectify,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((? [X3] : ((~l1_waybel_0(k1_funct_1(X2,X3),X1) | ~v7_waybel_0(k1_funct_1(X2,X3)) | ~v4_orders_2(k1_funct_1(X2,X3)) | v2_struct_0(k1_funct_1(X2,X3))) & r2_hidden(X3,X0)) | ~m3_yellow_6(X2,X0,X1)) & (! [X3] : ((l1_waybel_0(k1_funct_1(X2,X3),X1) & v7_waybel_0(k1_funct_1(X2,X3)) & v4_orders_2(k1_funct_1(X2,X3)) & ~v2_struct_0(k1_funct_1(X2,X3))) | ~r2_hidden(X3,X0)) | m3_yellow_6(X2,X0,X1)) & v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & l1_struct_0(X1))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (((? [X3] : ((~l1_waybel_0(k1_funct_1(X2,X3),X1) | ~v7_waybel_0(k1_funct_1(X2,X3)) | ~v4_orders_2(k1_funct_1(X2,X3)) | v2_struct_0(k1_funct_1(X2,X3))) & r2_hidden(X3,X0)) | ~m3_yellow_6(X2,X0,X1)) & (! [X3] : ((l1_waybel_0(k1_funct_1(X2,X3),X1) & v7_waybel_0(k1_funct_1(X2,X3)) & v4_orders_2(k1_funct_1(X2,X3)) & ~v2_struct_0(k1_funct_1(X2,X3))) | ~r2_hidden(X3,X0)) | m3_yellow_6(X2,X0,X1))) & v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & l1_struct_0(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((m3_yellow_6(X2,X0,X1) <~> ! [X3] : ((l1_waybel_0(k1_funct_1(X2,X3),X1) & v7_waybel_0(k1_funct_1(X2,X3)) & v4_orders_2(k1_funct_1(X2,X3)) & ~v2_struct_0(k1_funct_1(X2,X3))) | ~r2_hidden(X3,X0))) & v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & l1_struct_0(X1))),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((m3_yellow_6(X2,X0,X1) <~> ! [X3] : ((l1_waybel_0(k1_funct_1(X2,X3),X1) & v7_waybel_0(k1_funct_1(X2,X3)) & v4_orders_2(k1_funct_1(X2,X3)) & ~v2_struct_0(k1_funct_1(X2,X3))) | ~r2_hidden(X3,X0))) & (v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2))) & l1_struct_0(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (l1_struct_0(X1) => ! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) => (m3_yellow_6(X2,X0,X1) <=> ! [X3] : (r2_hidden(X3,X0) => (l1_waybel_0(k1_funct_1(X2,X3),X1) & v7_waybel_0(k1_funct_1(X2,X3)) & v4_orders_2(k1_funct_1(X2,X3)) & ~v2_struct_0(k1_funct_1(X2,X3)))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  % (28110)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (28110)Refutation not found, incomplete strategy% (28110)------------------------------
% 0.21/0.53  % (28110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28110)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28110)Memory used [KB]: 10618
% 0.21/0.53  % (28110)Time elapsed: 0.114 s
% 0.21/0.53  % (28110)------------------------------
% 0.21/0.53  % (28110)------------------------------
% 0.21/0.53  % (28109)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  fof(f5,conjecture,(
% 0.21/0.53    ! [X0,X1] : (l1_struct_0(X1) => ! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2)) => (m3_yellow_6(X2,X0,X1) <=> ! [X3] : (r2_hidden(X3,X0) => (l1_waybel_0(k1_funct_1(X2,X3),X1) & v7_waybel_0(k1_funct_1(X2,X3)) & v4_orders_2(k1_funct_1(X2,X3)) & ~v2_struct_0(k1_funct_1(X2,X3)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_yellow_6)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    v4_relat_1(sK2,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    l1_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f971,plain,(
% 0.21/0.53    ~spl8_27 | ~spl8_11 | spl8_61 | ~spl8_36),
% 0.21/0.53    inference(avatar_split_clause,[],[f962,f290,f525,f135,f211])).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    spl8_36 <=> r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 0.21/0.53  fof(f962,plain,(
% 0.21/0.53    sK4(sK1,sK2) = k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl8_36),
% 0.21/0.53    inference(resolution,[],[f292,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X5] : (k1_funct_1(X0,sK7(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK7(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2)) | ~spl8_36),
% 0.21/0.53    inference(avatar_component_clause,[],[f290])).
% 0.21/0.53  fof(f700,plain,(
% 0.21/0.53    ~spl8_27 | ~spl8_11 | ~spl8_36 | ~spl8_37 | ~spl8_10 | ~spl8_60),
% 0.21/0.53    inference(avatar_split_clause,[],[f681,f520,f107,f295,f290,f135,f211])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl8_10 <=> ! [X4] : (~v2_struct_0(k1_funct_1(sK2,X4)) | ~r2_hidden(X4,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.53  fof(f681,plain,(
% 0.21/0.53    ~v2_struct_0(sK4(sK1,sK2)) | ~r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_10 | ~spl8_60)),
% 0.21/0.53    inference(superposition,[],[f616,f65])).
% 0.21/0.53  fof(f616,plain,(
% 0.21/0.53    ~v2_struct_0(k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2)))) | (~spl8_10 | ~spl8_60)),
% 0.21/0.53    inference(resolution,[],[f522,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,sK0) | ~v2_struct_0(k1_funct_1(sK2,X4))) ) | ~spl8_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f107])).
% 0.21/0.53  fof(f695,plain,(
% 0.21/0.53    ~spl8_27 | ~spl8_11 | ~spl8_36 | spl8_39 | ~spl8_8 | ~spl8_60),
% 0.21/0.53    inference(avatar_split_clause,[],[f694,f520,f99,f303,f290,f135,f211])).
% 0.21/0.53  fof(f694,plain,(
% 0.21/0.53    v7_waybel_0(sK4(sK1,sK2)) | ~r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_8 | ~spl8_60)),
% 0.21/0.53    inference(superposition,[],[f618,f65])).
% 0.21/0.53  fof(f618,plain,(
% 0.21/0.53    v7_waybel_0(k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2)))) | (~spl8_8 | ~spl8_60)),
% 0.21/0.53    inference(resolution,[],[f522,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,sK0) | v7_waybel_0(k1_funct_1(sK2,X4))) ) | ~spl8_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f685,plain,(
% 0.21/0.53    ~spl8_27 | ~spl8_11 | ~spl8_36 | spl8_38 | ~spl8_9 | ~spl8_60),
% 0.21/0.53    inference(avatar_split_clause,[],[f684,f520,f103,f299,f290,f135,f211])).
% 0.21/0.53  fof(f684,plain,(
% 0.21/0.53    v4_orders_2(sK4(sK1,sK2)) | ~r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_9 | ~spl8_60)),
% 0.21/0.53    inference(superposition,[],[f617,f65])).
% 0.21/0.53  fof(f617,plain,(
% 0.21/0.53    v4_orders_2(k1_funct_1(sK2,sK7(sK2,sK4(sK1,sK2)))) | (~spl8_9 | ~spl8_60)),
% 0.21/0.53    inference(resolution,[],[f522,f104])).
% 0.21/0.53  fof(f588,plain,(
% 0.21/0.53    ~spl8_27 | ~spl8_11 | spl8_60 | ~spl8_33 | ~spl8_36),
% 0.21/0.53    inference(avatar_split_clause,[],[f587,f290,f256,f520,f135,f211])).
% 0.21/0.53  fof(f587,plain,(
% 0.21/0.53    r2_hidden(sK7(sK2,sK4(sK1,sK2)),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_33 | ~spl8_36)),
% 0.21/0.53    inference(forward_demodulation,[],[f578,f258])).
% 0.21/0.53  fof(f578,plain,(
% 0.21/0.53    r2_hidden(sK7(sK2,sK4(sK1,sK2)),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl8_36),
% 0.21/0.53    inference(resolution,[],[f292,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X5] : (r2_hidden(sK7(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X5,X1] : (r2_hidden(sK7(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f577,plain,(
% 0.21/0.53    spl8_4 | ~spl8_6 | ~spl8_8),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f575])).
% 0.21/0.53  fof(f575,plain,(
% 0.21/0.53    $false | (spl8_4 | ~spl8_6 | ~spl8_8)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f92,f83,f100])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ~v7_waybel_0(k1_funct_1(sK2,sK3)) | spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl8_4 <=> v7_waybel_0(k1_funct_1(sK2,sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f574,plain,(
% 0.21/0.53    ~spl8_35 | ~spl8_27 | ~spl8_34 | ~spl8_11 | ~spl8_28 | spl8_36 | spl8_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f572,f69,f290,f234,f135,f273,f211,f286])).
% 0.21/0.53  fof(f572,plain,(
% 0.21/0.53    r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2)) | ~v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~l1_struct_0(sK1) | spl8_1),
% 0.21/0.53    inference(resolution,[],[f71,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m3_yellow_6(X2,X0,X1) | r2_hidden(sK4(X1,X2),k2_relat_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~l1_struct_0(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f337,plain,(
% 0.21/0.53    spl8_35),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f334])).
% 0.21/0.53  fof(f334,plain,(
% 0.21/0.53    $false | spl8_35),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f34,f288])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    ~l1_struct_0(sK1) | spl8_35),
% 0.21/0.53    inference(avatar_component_clause,[],[f286])).
% 0.21/0.53  fof(f333,plain,(
% 0.21/0.53    spl8_34),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    $false | spl8_34),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f36,f275])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    ~v4_relat_1(sK2,sK0) | spl8_34),
% 0.21/0.53    inference(avatar_component_clause,[],[f273])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    spl8_28),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f320])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    $false | spl8_28),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f38,f236])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    ~v1_partfun1(sK2,sK0) | spl8_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f234])).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    spl8_27),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f311])).
% 0.21/0.53  fof(f311,plain,(
% 0.21/0.53    $false | spl8_27),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f35,f213])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | spl8_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f211])).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    ~spl8_27 | ~spl8_34 | spl8_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f271,f256,f273,f211])).
% 0.21/0.53  fof(f271,plain,(
% 0.21/0.53    sK0 = k1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.53    inference(resolution,[],[f38,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    spl8_11),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f260])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    $false | spl8_11),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f37,f137])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | spl8_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f135])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl8_1 | spl8_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f107,f69])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X4] : (~v2_struct_0(k1_funct_1(sK2,X4)) | ~r2_hidden(X4,sK0) | m3_yellow_6(sK2,sK0,sK1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl8_1 | spl8_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f40,f103,f69])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X4] : (v4_orders_2(k1_funct_1(sK2,X4)) | ~r2_hidden(X4,sK0) | m3_yellow_6(sK2,sK0,sK1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl8_1 | spl8_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f99,f69])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X4] : (v7_waybel_0(k1_funct_1(sK2,X4)) | ~r2_hidden(X4,sK0) | m3_yellow_6(sK2,sK0,sK1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl8_1 | spl8_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f42,f95,f69])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X4] : (l1_waybel_0(k1_funct_1(sK2,X4),sK1) | ~r2_hidden(X4,sK0) | m3_yellow_6(sK2,sK0,sK1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ~spl8_1 | spl8_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f43,f90,f69])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    r2_hidden(sK3,sK0) | ~m3_yellow_6(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4 | ~spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f85,f81,f77,f73,f69])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ~l1_waybel_0(k1_funct_1(sK2,sK3),sK1) | ~v7_waybel_0(k1_funct_1(sK2,sK3)) | ~v4_orders_2(k1_funct_1(sK2,sK3)) | v2_struct_0(k1_funct_1(sK2,sK3)) | ~m3_yellow_6(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (28100)------------------------------
% 0.21/0.53  % (28100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28100)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (28100)Memory used [KB]: 7036
% 0.21/0.53  % (28100)Time elapsed: 0.064 s
% 0.21/0.53  % (28100)------------------------------
% 0.21/0.53  % (28100)------------------------------
% 0.21/0.54  % (28101)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.54  % (28089)Success in time 0.176 s
%------------------------------------------------------------------------------
