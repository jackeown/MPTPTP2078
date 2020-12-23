%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1945+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:56 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  311 ( 766 expanded)
%              Number of leaves         :   75 ( 356 expanded)
%              Depth                    :   14
%              Number of atoms          : 1603 (6126 expanded)
%              Number of equality atoms :   42 ( 420 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f906,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f162,f181,f192,f194,f196,f208,f210,f216,f239,f241,f255,f257,f259,f268,f277,f293,f298,f305,f310,f328,f352,f417,f422,f429,f439,f441,f451,f466,f507,f571,f573,f594,f597,f636,f795,f815,f826,f903,f905])).

fof(f905,plain,
    ( ~ spl22_5
    | ~ spl22_73
    | ~ spl22_55
    | spl22_87 ),
    inference(avatar_split_clause,[],[f904,f900,f622,f805,f185])).

fof(f185,plain,
    ( spl22_5
  <=> sP0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_5])])).

fof(f805,plain,
    ( spl22_73
  <=> m1_subset_1(sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_73])])).

fof(f622,plain,
    ( spl22_55
  <=> m1_subset_1(sK9,u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_55])])).

fof(f900,plain,
    ( spl22_87
  <=> m1_subset_1(sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),sK9),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_87])])).

fof(f904,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),u1_struct_0(sK7))
    | ~ sP0(sK7)
    | spl22_87 ),
    inference(resolution,[],[f902,f107])).

fof(f107,plain,(
    ! [X4,X0,X5] :
      ( m1_subset_1(sK12(X0,X4,X5),u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ! [X3] :
              ( ~ r1_orders_2(X0,sK11(X0),X3)
              | ~ r1_orders_2(X0,sK10(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(sK11(X0),u1_struct_0(X0))
          & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( ( r1_orders_2(X0,X5,sK12(X0,X4,X5))
                  & r1_orders_2(X0,X4,sK12(X0,X4,X5))
                  & m1_subset_1(sK12(X0,X4,X5),u1_struct_0(X0)) )
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f57,f60,f59,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK10(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,sK10(X0),X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_orders_2(X0,sK11(X0),X3)
            | ~ r1_orders_2(X0,sK10(X0),X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK11(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X5,X4,X0] :
      ( ? [X6] :
          ( r1_orders_2(X0,X5,X6)
          & r1_orders_2(X0,X4,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X5,sK12(X0,X4,X5))
        & r1_orders_2(X0,X4,sK12(X0,X4,X5))
        & m1_subset_1(sK12(X0,X4,X5),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X4] :
            ( ! [X5] :
                ( ? [X6] :
                    ( r1_orders_2(X0,X5,X6)
                    & r1_orders_2(X0,X4,X6)
                    & m1_subset_1(X6,u1_struct_0(X0)) )
                | ~ m1_subset_1(X5,u1_struct_0(X0)) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    | ~ r1_orders_2(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f902,plain,
    ( ~ m1_subset_1(sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),sK9),u1_struct_0(sK7))
    | spl22_87 ),
    inference(avatar_component_clause,[],[f900])).

fof(f903,plain,
    ( ~ spl22_5
    | ~ spl22_73
    | ~ spl22_87
    | ~ spl22_55
    | ~ spl22_75 ),
    inference(avatar_split_clause,[],[f898,f813,f622,f900,f805,f185])).

fof(f813,plain,
    ( spl22_75
  <=> ! [X2] :
        ( ~ r1_orders_2(sK7,sK9,sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK7))
        | ~ m1_subset_1(sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X2),u1_struct_0(sK7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_75])])).

fof(f898,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),u1_struct_0(sK7))
    | ~ sP0(sK7)
    | ~ spl22_75 ),
    inference(duplicate_literal_removal,[],[f897])).

fof(f897,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),sK9),u1_struct_0(sK7))
    | ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | ~ m1_subset_1(sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),u1_struct_0(sK7))
    | ~ sP0(sK7)
    | ~ spl22_75 ),
    inference(resolution,[],[f814,f109])).

fof(f109,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X5,sK12(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f814,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK7,sK9,sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK7))
        | ~ m1_subset_1(sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X2),u1_struct_0(sK7)) )
    | ~ spl22_75 ),
    inference(avatar_component_clause,[],[f813])).

fof(f826,plain,
    ( ~ spl22_1
    | spl22_2
    | ~ spl22_51
    | ~ spl22_48
    | ~ spl22_9
    | ~ spl22_22
    | ~ spl22_28
    | spl22_73 ),
    inference(avatar_split_clause,[],[f825,f805,f350,f302,f213,f568,f588,f159,f155])).

fof(f155,plain,
    ( spl22_1
  <=> m1_subset_1(a_3_1_yellow_6(sK6,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_1])])).

fof(f159,plain,
    ( spl22_2
  <=> r2_hidden(sK8,k2_pre_topc(sK6,a_3_1_yellow_6(sK6,sK7,sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_2])])).

fof(f588,plain,
    ( spl22_51
  <=> r2_hidden(sK8,k10_yellow_6(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_51])])).

fof(f568,plain,
    ( spl22_48
  <=> m1_subset_1(sK8,u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_48])])).

fof(f213,plain,
    ( spl22_9
  <=> sP3(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_9])])).

fof(f302,plain,
    ( spl22_22
  <=> sP4(sK7,sK6,k10_yellow_6(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_22])])).

fof(f350,plain,
    ( spl22_28
  <=> ! [X1,X0] :
        ( m1_connsp_2(sK15(sK6,X0,X1),sK6,X1)
        | r2_hidden(X1,k2_pre_topc(sK6,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X1,u1_struct_0(sK6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_28])])).

fof(f825,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | ~ r2_hidden(sK8,k10_yellow_6(sK6,sK7))
    | r2_hidden(sK8,k2_pre_topc(sK6,a_3_1_yellow_6(sK6,sK7,sK9)))
    | ~ m1_subset_1(a_3_1_yellow_6(sK6,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl22_9
    | ~ spl22_22
    | ~ spl22_28
    | spl22_73 ),
    inference(resolution,[],[f824,f382])).

fof(f382,plain,
    ( ! [X0,X1] :
        ( sP2(sK15(sK6,X0,X1),sK7,sK6)
        | ~ m1_subset_1(X1,u1_struct_0(sK6))
        | ~ r2_hidden(X1,k10_yellow_6(sK6,sK7))
        | r2_hidden(X1,k2_pre_topc(sK6,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) )
    | ~ spl22_9
    | ~ spl22_22
    | ~ spl22_28 ),
    inference(resolution,[],[f354,f218])).

fof(f218,plain,
    ( ! [X1] :
        ( ~ r1_waybel_0(sK6,sK7,X1)
        | sP2(X1,sK7,sK6) )
    | ~ spl22_9 ),
    inference(resolution,[],[f215,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1)
      | ~ r1_waybel_0(X0,X1,X2)
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_waybel_0(X0,X1,X2)
            | ~ sP2(X2,X1,X0) )
          & ( sP2(X2,X1,X0)
            | ~ r1_waybel_0(X0,X1,X2) ) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_waybel_0(X0,X1,X2)
        <=> sP2(X2,X1,X0) )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f215,plain,
    ( sP3(sK6,sK7)
    | ~ spl22_9 ),
    inference(avatar_component_clause,[],[f213])).

fof(f354,plain,
    ( ! [X0,X1] :
        ( r1_waybel_0(sK6,sK7,sK15(sK6,X1,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(X0,k10_yellow_6(sK6,sK7))
        | r2_hidden(X0,k2_pre_topc(sK6,X1)) )
    | ~ spl22_22
    | ~ spl22_28 ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k2_pre_topc(sK6,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(X0,k10_yellow_6(sK6,sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | r1_waybel_0(sK6,sK7,sK15(sK6,X1,X0)) )
    | ~ spl22_22
    | ~ spl22_28 ),
    inference(resolution,[],[f351,f311])).

fof(f311,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK6,X1)
        | ~ r2_hidden(X1,k10_yellow_6(sK6,sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK6))
        | r1_waybel_0(sK6,sK7,X0) )
    | ~ spl22_22 ),
    inference(resolution,[],[f304,f127])).

fof(f127,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ m1_connsp_2(X8,X1,X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | r1_waybel_0(X1,X0,X8) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ( ( ~ r1_waybel_0(X1,X0,sK17(X0,X1,X2))
              & m1_connsp_2(sK17(X0,X1,X2),X1,sK16(X0,X1,X2)) )
            | ~ r2_hidden(sK16(X0,X1,X2),X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X1,X0,X5)
                | ~ m1_connsp_2(X5,X1,sK16(X0,X1,X2)) )
            | r2_hidden(sK16(X0,X1,X2),X2) )
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ( ~ r1_waybel_0(X1,X0,sK18(X0,X1,X6))
                  & m1_connsp_2(sK18(X0,X1,X6),X1,X6) ) )
              & ( ! [X8] :
                    ( r1_waybel_0(X1,X0,X8)
                    | ~ m1_connsp_2(X8,X1,X6) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18])],[f76,f79,f78,f77])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X1,X0,X4)
                & m1_connsp_2(X4,X1,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X1,X0,X5)
                | ~ m1_connsp_2(X5,X1,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X1,X0,X4)
              & m1_connsp_2(X4,X1,sK16(X0,X1,X2)) )
          | ~ r2_hidden(sK16(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X1,X0,X5)
              | ~ m1_connsp_2(X5,X1,sK16(X0,X1,X2)) )
          | r2_hidden(sK16(X0,X1,X2),X2) )
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X1,X0,X4)
          & m1_connsp_2(X4,X1,sK16(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X1,X0,sK17(X0,X1,X2))
        & m1_connsp_2(sK17(X0,X1,X2),X1,sK16(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X1,X0,X7)
          & m1_connsp_2(X7,X1,X6) )
     => ( ~ r1_waybel_0(X1,X0,sK18(X0,X1,X6))
        & m1_connsp_2(sK18(X0,X1,X6),X1,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_waybel_0(X1,X0,X4)
                  & m1_connsp_2(X4,X1,X3) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X5] :
                  ( r1_waybel_0(X1,X0,X5)
                  | ~ m1_connsp_2(X5,X1,X3) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X6] :
            ( ( ( r2_hidden(X6,X2)
                | ? [X7] :
                    ( ~ r1_waybel_0(X1,X0,X7)
                    & m1_connsp_2(X7,X1,X6) ) )
              & ( ! [X8] :
                    ( r1_waybel_0(X1,X0,X8)
                    | ~ m1_connsp_2(X8,X1,X6) )
                | ~ r2_hidden(X6,X2) ) )
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_waybel_0(X0,X1,X4)
                  & m1_connsp_2(X4,X0,X3) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X4] :
                  ( r1_waybel_0(X0,X1,X4)
                  | ~ m1_connsp_2(X4,X0,X3) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ? [X4] :
                    ( ~ r1_waybel_0(X0,X1,X4)
                    & m1_connsp_2(X4,X0,X3) ) )
              & ( ! [X4] :
                    ( r1_waybel_0(X0,X1,X4)
                    | ~ m1_connsp_2(X4,X0,X3) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ? [X3] :
            ( ( ? [X4] :
                  ( ~ r1_waybel_0(X0,X1,X4)
                  & m1_connsp_2(X4,X0,X3) )
              | ~ r2_hidden(X3,X2) )
            & ( ! [X4] :
                  ( r1_waybel_0(X0,X1,X4)
                  | ~ m1_connsp_2(X4,X0,X3) )
              | r2_hidden(X3,X2) )
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ? [X4] :
                    ( ~ r1_waybel_0(X0,X1,X4)
                    & m1_connsp_2(X4,X0,X3) ) )
              & ( ! [X4] :
                    ( r1_waybel_0(X0,X1,X4)
                    | ~ m1_connsp_2(X4,X0,X3) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( sP4(X1,X0,X2)
    <=> ! [X3] :
          ( ( r2_hidden(X3,X2)
          <=> ! [X4] :
                ( r1_waybel_0(X0,X1,X4)
                | ~ m1_connsp_2(X4,X0,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f304,plain,
    ( sP4(sK7,sK6,k10_yellow_6(sK6,sK7))
    | ~ spl22_22 ),
    inference(avatar_component_clause,[],[f302])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( m1_connsp_2(sK15(sK6,X0,X1),sK6,X1)
        | r2_hidden(X1,k2_pre_topc(sK6,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X1,u1_struct_0(sK6)) )
    | ~ spl22_28 ),
    inference(avatar_component_clause,[],[f350])).

fof(f824,plain,
    ( ~ sP2(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6)
    | spl22_73 ),
    inference(resolution,[],[f807,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_hidden(k2_waybel_0(X2,X1,sK13(X0,X1,X2,X3)),X0)
              & r1_orders_2(X1,X3,sK13(X0,X1,X2,X3))
              & m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X1)) )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
              | ~ r1_orders_2(X1,sK14(X0,X1,X2),X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14])],[f64,f66,f65])).

fof(f65,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X2,X1,sK13(X0,X1,X2,X3)),X0)
        & r1_orders_2(X1,X3,sK13(X0,X1,X2,X3))
        & m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
            | ~ r1_orders_2(X1,sK14(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
                | ~ r1_orders_2(X1,X5,X6)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ( sP2(X2,X1,X0)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                | ~ r1_orders_2(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP2(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( sP2(X2,X1,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f807,plain,
    ( ~ m1_subset_1(sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),u1_struct_0(sK7))
    | spl22_73 ),
    inference(avatar_component_clause,[],[f805])).

fof(f815,plain,
    ( ~ spl22_5
    | ~ spl22_73
    | spl22_75
    | ~ spl22_71 ),
    inference(avatar_split_clause,[],[f801,f793,f813,f805,f185])).

fof(f793,plain,
    ( spl22_71
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ r1_orders_2(sK7,sK9,X0)
        | ~ r1_orders_2(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_71])])).

fof(f801,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK7,sK9,sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X2))
        | ~ m1_subset_1(sK12(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X2),u1_struct_0(sK7))
        | ~ m1_subset_1(X2,u1_struct_0(sK7))
        | ~ m1_subset_1(sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),u1_struct_0(sK7))
        | ~ sP0(sK7) )
    | ~ spl22_71 ),
    inference(resolution,[],[f794,f108])).

fof(f108,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X4,sK12(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f794,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X0)
        | ~ r1_orders_2(sK7,sK9,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK7)) )
    | ~ spl22_71 ),
    inference(avatar_component_clause,[],[f793])).

fof(f795,plain,
    ( ~ spl22_55
    | spl22_71
    | ~ spl22_42
    | ~ spl22_52 ),
    inference(avatar_split_clause,[],[f791,f592,f505,f793,f622])).

fof(f505,plain,
    ( spl22_42
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK7,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | r2_hidden(k2_waybel_0(sK6,sK7,X1),a_3_1_yellow_6(sK6,sK7,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_42])])).

fof(f592,plain,
    ( spl22_52
  <=> ! [X2] :
        ( ~ r2_hidden(k2_waybel_0(sK6,sK7,X2),a_3_1_yellow_6(sK6,sK7,sK9))
        | ~ m1_subset_1(X2,u1_struct_0(sK7))
        | ~ r1_orders_2(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_52])])).

fof(f791,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ r1_orders_2(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X0)
        | ~ m1_subset_1(sK9,u1_struct_0(sK7))
        | ~ r1_orders_2(sK7,sK9,X0) )
    | ~ spl22_42
    | ~ spl22_52 ),
    inference(duplicate_literal_removal,[],[f788])).

fof(f788,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ r1_orders_2(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ m1_subset_1(sK9,u1_struct_0(sK7))
        | ~ r1_orders_2(sK7,sK9,X0) )
    | ~ spl22_42
    | ~ spl22_52 ),
    inference(resolution,[],[f593,f506])).

fof(f506,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_waybel_0(sK6,sK7,X1),a_3_1_yellow_6(sK6,sK7,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ r1_orders_2(sK7,X0,X1) )
    | ~ spl22_42 ),
    inference(avatar_component_clause,[],[f505])).

fof(f593,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k2_waybel_0(sK6,sK7,X2),a_3_1_yellow_6(sK6,sK7,sK9))
        | ~ m1_subset_1(X2,u1_struct_0(sK7))
        | ~ r1_orders_2(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X2) )
    | ~ spl22_52 ),
    inference(avatar_component_clause,[],[f592])).

fof(f636,plain,(
    spl22_55 ),
    inference(avatar_contradiction_clause,[],[f635])).

fof(f635,plain,
    ( $false
    | spl22_55 ),
    inference(resolution,[],[f624,f101])).

fof(f101,plain,(
    m1_subset_1(sK9,u1_struct_0(sK7)) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK8,k2_pre_topc(sK6,X4))
        | a_3_1_yellow_6(sK6,sK7,sK9) != X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) )
    & m1_subset_1(sK9,u1_struct_0(sK7))
    & r2_hidden(sK8,k10_yellow_6(sK6,sK7))
    & m1_subset_1(sK8,u1_struct_0(sK6))
    & l1_waybel_0(sK7,sK6)
    & v7_waybel_0(sK7)
    & v4_orders_2(sK7)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f19,f53,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
                        | a_3_1_yellow_6(X0,X1,X3) != X4
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                & r2_hidden(X2,k10_yellow_6(X0,X1))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k2_pre_topc(sK6,X4))
                      | a_3_1_yellow_6(sK6,X1,X3) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & r2_hidden(X2,k10_yellow_6(sK6,X1))
              & m1_subset_1(X2,u1_struct_0(sK6)) )
          & l1_waybel_0(X1,sK6)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r2_hidden(X2,k2_pre_topc(sK6,X4))
                    | a_3_1_yellow_6(sK6,X1,X3) != X4
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) )
                & m1_subset_1(X3,u1_struct_0(X1)) )
            & r2_hidden(X2,k10_yellow_6(sK6,X1))
            & m1_subset_1(X2,u1_struct_0(sK6)) )
        & l1_waybel_0(X1,sK6)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X2,k2_pre_topc(sK6,X4))
                  | a_3_1_yellow_6(sK6,sK7,X3) != X4
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) )
              & m1_subset_1(X3,u1_struct_0(sK7)) )
          & r2_hidden(X2,k10_yellow_6(sK6,sK7))
          & m1_subset_1(X2,u1_struct_0(sK6)) )
      & l1_waybel_0(sK7,sK6)
      & v7_waybel_0(sK7)
      & v4_orders_2(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X2,k2_pre_topc(sK6,X4))
                | a_3_1_yellow_6(sK6,sK7,X3) != X4
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) )
            & m1_subset_1(X3,u1_struct_0(sK7)) )
        & r2_hidden(X2,k10_yellow_6(sK6,sK7))
        & m1_subset_1(X2,u1_struct_0(sK6)) )
   => ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(sK8,k2_pre_topc(sK6,X4))
              | a_3_1_yellow_6(sK6,sK7,X3) != X4
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) )
          & m1_subset_1(X3,u1_struct_0(sK7)) )
      & r2_hidden(sK8,k10_yellow_6(sK6,sK7))
      & m1_subset_1(sK8,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( ~ r2_hidden(sK8,k2_pre_topc(sK6,X4))
            | a_3_1_yellow_6(sK6,sK7,X3) != X4
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) )
        & m1_subset_1(X3,u1_struct_0(sK7)) )
   => ( ! [X4] :
          ( ~ r2_hidden(sK8,k2_pre_topc(sK6,X4))
          | a_3_1_yellow_6(sK6,sK7,sK9) != X4
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) )
      & m1_subset_1(sK9,u1_struct_0(sK7)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
                      | a_3_1_yellow_6(X0,X1,X3) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_hidden(X2,k2_pre_topc(X0,X4))
                      | a_3_1_yellow_6(X0,X1,X3) != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & r2_hidden(X2,k10_yellow_6(X0,X1))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,X1))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ? [X4] :
                          ( r2_hidden(X2,k2_pre_topc(X0,X4))
                          & a_3_1_yellow_6(X0,X1,X3) = X4
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ? [X4] :
                        ( r2_hidden(X2,k2_pre_topc(X0,X4))
                        & a_3_1_yellow_6(X0,X1,X3) = X4
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_yellow_6)).

fof(f624,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | spl22_55 ),
    inference(avatar_component_clause,[],[f622])).

fof(f597,plain,(
    spl22_51 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | spl22_51 ),
    inference(resolution,[],[f590,f100])).

fof(f100,plain,(
    r2_hidden(sK8,k10_yellow_6(sK6,sK7)) ),
    inference(cnf_transformation,[],[f54])).

fof(f590,plain,
    ( ~ r2_hidden(sK8,k10_yellow_6(sK6,sK7))
    | spl22_51 ),
    inference(avatar_component_clause,[],[f588])).

fof(f594,plain,
    ( ~ spl22_48
    | ~ spl22_1
    | spl22_2
    | ~ spl22_51
    | spl22_52
    | ~ spl22_9
    | ~ spl22_22
    | ~ spl22_28
    | ~ spl22_47 ),
    inference(avatar_split_clause,[],[f575,f565,f350,f302,f213,f592,f588,f159,f155,f568])).

fof(f565,plain,
    ( spl22_47
  <=> ! [X4] :
        ( ~ r2_hidden(X4,a_3_1_yellow_6(sK6,sK7,sK9))
        | ~ r2_hidden(X4,sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_47])])).

fof(f575,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k2_waybel_0(sK6,sK7,X2),a_3_1_yellow_6(sK6,sK7,sK9))
        | ~ r2_hidden(sK8,k10_yellow_6(sK6,sK7))
        | r2_hidden(sK8,k2_pre_topc(sK6,a_3_1_yellow_6(sK6,sK7,sK9)))
        | ~ m1_subset_1(a_3_1_yellow_6(sK6,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ r1_orders_2(sK7,sK14(sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8),sK7,sK6),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK7))
        | ~ m1_subset_1(sK8,u1_struct_0(sK6)) )
    | ~ spl22_9
    | ~ spl22_22
    | ~ spl22_28
    | ~ spl22_47 ),
    inference(resolution,[],[f566,f384])).

fof(f384,plain,
    ( ! [X4,X2,X3] :
        ( r2_hidden(k2_waybel_0(sK6,sK7,X4),sK15(sK6,X3,X2))
        | ~ r2_hidden(X2,k10_yellow_6(sK6,sK7))
        | r2_hidden(X2,k2_pre_topc(sK6,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ r1_orders_2(sK7,sK14(sK15(sK6,X3,X2),sK7,sK6),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK7))
        | ~ m1_subset_1(X2,u1_struct_0(sK6)) )
    | ~ spl22_9
    | ~ spl22_22
    | ~ spl22_28 ),
    inference(resolution,[],[f382,f117])).

fof(f117,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r1_orders_2(X1,sK14(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X2,X1,X6),X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f566,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8))
        | ~ r2_hidden(X4,a_3_1_yellow_6(sK6,sK7,sK9)) )
    | ~ spl22_47 ),
    inference(avatar_component_clause,[],[f565])).

fof(f573,plain,(
    spl22_48 ),
    inference(avatar_contradiction_clause,[],[f572])).

fof(f572,plain,
    ( $false
    | spl22_48 ),
    inference(resolution,[],[f570,f99])).

fof(f99,plain,(
    m1_subset_1(sK8,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f54])).

fof(f570,plain,
    ( ~ m1_subset_1(sK8,u1_struct_0(sK6))
    | spl22_48 ),
    inference(avatar_component_clause,[],[f568])).

fof(f571,plain,
    ( spl22_47
    | ~ spl22_48
    | ~ spl22_1
    | spl22_2
    | ~ spl22_23 ),
    inference(avatar_split_clause,[],[f562,f308,f159,f155,f568,f565])).

fof(f308,plain,
    ( spl22_23
  <=> ! [X1,X0] :
        ( r1_xboole_0(sK15(sK6,X0,X1),X0)
        | r2_hidden(X1,k2_pre_topc(sK6,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X1,u1_struct_0(sK6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_23])])).

fof(f562,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK8,u1_struct_0(sK6))
        | ~ r2_hidden(X4,a_3_1_yellow_6(sK6,sK7,sK9))
        | ~ r2_hidden(X4,sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),sK8)) )
    | ~ spl22_1
    | spl22_2
    | ~ spl22_23 ),
    inference(resolution,[],[f467,f161])).

fof(f161,plain,
    ( ~ r2_hidden(sK8,k2_pre_topc(sK6,a_3_1_yellow_6(sK6,sK7,sK9)))
    | spl22_2 ),
    inference(avatar_component_clause,[],[f159])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k2_pre_topc(sK6,a_3_1_yellow_6(sK6,sK7,sK9)))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(X1,a_3_1_yellow_6(sK6,sK7,sK9))
        | ~ r2_hidden(X1,sK15(sK6,a_3_1_yellow_6(sK6,sK7,sK9),X0)) )
    | ~ spl22_1
    | ~ spl22_23 ),
    inference(resolution,[],[f156,f316])).

fof(f316,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
        | r2_hidden(X0,k2_pre_topc(sK6,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,sK15(sK6,X1,X0)) )
    | ~ spl22_23 ),
    inference(resolution,[],[f309,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK19(X0,X1),X1)
          & r2_hidden(sK19(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f30,f81])).

fof(f81,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK19(X0,X1),X1)
        & r2_hidden(sK19(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f309,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(sK15(sK6,X0,X1),X0)
        | r2_hidden(X1,k2_pre_topc(sK6,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X1,u1_struct_0(sK6)) )
    | ~ spl22_23 ),
    inference(avatar_component_clause,[],[f308])).

fof(f156,plain,
    ( m1_subset_1(a_3_1_yellow_6(sK6,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl22_1 ),
    inference(avatar_component_clause,[],[f155])).

fof(f507,plain,
    ( ~ spl22_15
    | spl22_42
    | ~ spl22_16
    | spl22_7
    | ~ spl22_38 ),
    inference(avatar_split_clause,[],[f503,f449,f202,f252,f505,f248])).

fof(f248,plain,
    ( spl22_15
  <=> l1_waybel_0(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_15])])).

fof(f252,plain,
    ( spl22_16
  <=> v2_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_16])])).

fof(f202,plain,
    ( spl22_7
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_7])])).

fof(f449,plain,
    ( spl22_38
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK7,X0,X1)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | r2_hidden(k2_waybel_0(X2,sK7,X1),a_3_1_yellow_6(X2,sK7,X0))
        | ~ l1_waybel_0(sK7,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_38])])).

% (22911)Refutation not found, incomplete strategy% (22911)------------------------------
% (22911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22911)Termination reason: Refutation not found, incomplete strategy

% (22911)Memory used [KB]: 10874
% (22911)Time elapsed: 0.186 s
% (22911)------------------------------
% (22911)------------------------------
fof(f503,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK6)
        | ~ v2_pre_topc(sK6)
        | ~ r1_orders_2(sK7,X0,X1)
        | r2_hidden(k2_waybel_0(sK6,sK7,X1),a_3_1_yellow_6(sK6,sK7,X0))
        | ~ l1_waybel_0(sK7,sK6)
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK7)) )
    | ~ spl22_38 ),
    inference(resolution,[],[f450,f94])).

fof(f94,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f450,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X2)
        | v2_struct_0(X2)
        | ~ v2_pre_topc(X2)
        | ~ r1_orders_2(sK7,X0,X1)
        | r2_hidden(k2_waybel_0(X2,sK7,X1),a_3_1_yellow_6(X2,sK7,X0))
        | ~ l1_waybel_0(sK7,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK7)) )
    | ~ spl22_38 ),
    inference(avatar_component_clause,[],[f449])).

fof(f466,plain,
    ( spl22_1
    | ~ spl22_17
    | ~ spl22_37 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | spl22_1
    | ~ spl22_17
    | ~ spl22_37 ),
    inference(resolution,[],[f461,f101])).

fof(f461,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK7))
    | spl22_1
    | ~ spl22_17
    | ~ spl22_37 ),
    inference(resolution,[],[f460,f157])).

fof(f157,plain,
    ( ~ m1_subset_1(a_3_1_yellow_6(sK6,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK6)))
    | spl22_1 ),
    inference(avatar_component_clause,[],[f155])).

fof(f460,plain,
    ( ! [X2] :
        ( m1_subset_1(a_3_1_yellow_6(sK6,sK7,X2),k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
    | ~ spl22_17
    | ~ spl22_37 ),
    inference(duplicate_literal_removal,[],[f459])).

fof(f459,plain,
    ( ! [X2] :
        ( m1_subset_1(a_3_1_yellow_6(sK6,sK7,X2),k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X2,u1_struct_0(sK7))
        | m1_subset_1(a_3_1_yellow_6(sK6,sK7,X2),k1_zfmisc_1(u1_struct_0(sK6))) )
    | ~ spl22_17
    | ~ spl22_37 ),
    inference(resolution,[],[f454,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f454,plain,
    ( ! [X0] :
        ( r1_tarski(a_3_1_yellow_6(sK6,sK7,X0),u1_struct_0(sK6))
        | m1_subset_1(a_3_1_yellow_6(sK6,sK7,X0),k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ m1_subset_1(X0,u1_struct_0(sK7)) )
    | ~ spl22_17
    | ~ spl22_37 ),
    inference(resolution,[],[f453,f271])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK20(X0,u1_struct_0(sK6)),u1_struct_0(sK6))
        | r1_tarski(X0,u1_struct_0(sK6)) )
    | ~ spl22_17 ),
    inference(resolution,[],[f264,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK20(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK20(X0,X1),X1)
          & r2_hidden(sK20(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f84,f85])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK20(X0,X1),X1)
        & r2_hidden(sK20(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f264,plain,
    ( ! [X1] :
        ( r2_hidden(X1,u1_struct_0(sK6))
        | ~ m1_subset_1(X1,u1_struct_0(sK6)) )
    | ~ spl22_17 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl22_17
  <=> ! [X1] :
        ( r2_hidden(X1,u1_struct_0(sK6))
        | ~ m1_subset_1(X1,u1_struct_0(sK6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_17])])).

fof(f453,plain,
    ( ! [X4,X3] :
        ( m1_subset_1(sK20(a_3_1_yellow_6(sK6,sK7,X3),X4),u1_struct_0(sK6))
        | ~ m1_subset_1(X3,u1_struct_0(sK7))
        | m1_subset_1(a_3_1_yellow_6(sK6,sK7,X3),k1_zfmisc_1(X4)) )
    | ~ spl22_37 ),
    inference(resolution,[],[f446,f144])).

fof(f446,plain,
    ( ! [X12,X11] :
        ( r1_tarski(a_3_1_yellow_6(sK6,sK7,X11),X12)
        | ~ m1_subset_1(X11,u1_struct_0(sK7))
        | m1_subset_1(sK20(a_3_1_yellow_6(sK6,sK7,X11),X12),u1_struct_0(sK6)) )
    | ~ spl22_37 ),
    inference(resolution,[],[f438,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK20(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f438,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_3_1_yellow_6(sK6,sK7,X1))
        | m1_subset_1(X0,u1_struct_0(sK6))
        | ~ m1_subset_1(X1,u1_struct_0(sK7)) )
    | ~ spl22_37 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl22_37
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,a_3_1_yellow_6(sK6,sK7,X1))
        | m1_subset_1(X0,u1_struct_0(sK6))
        | ~ m1_subset_1(X1,u1_struct_0(sK7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_37])])).

fof(f451,plain,
    ( spl22_4
    | ~ spl22_12
    | spl22_38 ),
    inference(avatar_split_clause,[],[f447,f449,f233,f178])).

fof(f178,plain,
    ( spl22_4
  <=> v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_4])])).

fof(f233,plain,
    ( spl22_12
  <=> v4_orders_2(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_12])])).

fof(f447,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK7,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK7))
      | ~ m1_subset_1(X0,u1_struct_0(sK7))
      | ~ l1_waybel_0(sK7,X2)
      | r2_hidden(k2_waybel_0(X2,sK7,X1),a_3_1_yellow_6(X2,sK7,X0))
      | ~ v4_orders_2(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f153,f97])).

fof(f97,plain,(
    v7_waybel_0(sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f153,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ v7_waybel_0(X2)
      | ~ r1_orders_2(X2,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | r2_hidden(k2_waybel_0(X1,X2,X4),a_3_1_yellow_6(X1,X2,X3))
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f150])).

fof(f150,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      | ~ r1_orders_2(X2,X3,X4)
      | k2_waybel_0(X1,X2,X4) != X0
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | k2_waybel_0(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ( r1_orders_2(X2,X3,sK21(X0,X1,X2,X3))
            & k2_waybel_0(X1,X2,sK21(X0,X1,X2,X3)) = X0
            & m1_subset_1(sK21(X0,X1,X2,X3),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f89,f90])).

fof(f90,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r1_orders_2(X2,X3,X5)
          & k2_waybel_0(X1,X2,X5) = X0
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( r1_orders_2(X2,X3,sK21(X0,X1,X2,X3))
        & k2_waybel_0(X1,X2,sK21(X0,X1,X2,X3)) = X0
        & m1_subset_1(sK21(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | k2_waybel_0(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X5] :
              ( r1_orders_2(X2,X3,X5)
              & k2_waybel_0(X1,X2,X5) = X0
              & m1_subset_1(X5,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
          | ! [X4] :
              ( ~ r1_orders_2(X2,X3,X4)
              | k2_waybel_0(X1,X2,X4) != X0
              | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r1_orders_2(X2,X3,X4)
              & k2_waybel_0(X1,X2,X4) = X0
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & k2_waybel_0(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & k2_waybel_0(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X2)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X2))
        & l1_waybel_0(X2,X1)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      <=> ? [X4] :
            ( r1_orders_2(X2,X3,X4)
            & k2_waybel_0(X1,X2,X4) = X0
            & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_1_yellow_6)).

fof(f441,plain,(
    spl22_36 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | spl22_36 ),
    inference(resolution,[],[f435,f94])).

fof(f435,plain,
    ( ~ l1_pre_topc(sK6)
    | spl22_36 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl22_36
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_36])])).

fof(f439,plain,
    ( spl22_7
    | ~ spl22_16
    | ~ spl22_36
    | spl22_4
    | ~ spl22_12
    | ~ spl22_6
    | ~ spl22_15
    | spl22_37
    | ~ spl22_35 ),
    inference(avatar_split_clause,[],[f431,f427,f437,f248,f189,f233,f178,f433,f252,f202])).

fof(f189,plain,
    ( spl22_6
  <=> v7_waybel_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_6])])).

fof(f427,plain,
    ( spl22_35
  <=> ! [X7,X6] :
        ( m1_subset_1(X6,u1_struct_0(sK6))
        | ~ r2_hidden(X6,a_3_1_yellow_6(sK6,sK7,X7))
        | ~ m1_subset_1(X7,u1_struct_0(sK7))
        | ~ m1_subset_1(sK21(X6,sK6,sK7,X7),u1_struct_0(sK7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_35])])).

fof(f431,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_3_1_yellow_6(sK6,sK7,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK7))
        | m1_subset_1(X0,u1_struct_0(sK6))
        | ~ l1_waybel_0(sK7,sK6)
        | ~ v7_waybel_0(sK7)
        | ~ v4_orders_2(sK7)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | ~ spl22_35 ),
    inference(duplicate_literal_removal,[],[f430])).

fof(f430,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,a_3_1_yellow_6(sK6,sK7,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK7))
        | m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(X0,a_3_1_yellow_6(sK6,sK7,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK7))
        | ~ l1_waybel_0(sK7,sK6)
        | ~ v7_waybel_0(sK7)
        | ~ v4_orders_2(sK7)
        | v2_struct_0(sK7)
        | ~ l1_pre_topc(sK6)
        | ~ v2_pre_topc(sK6)
        | v2_struct_0(sK6) )
    | ~ spl22_35 ),
    inference(resolution,[],[f428,f147])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK21(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | ~ v7_waybel_0(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f428,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(sK21(X6,sK6,sK7,X7),u1_struct_0(sK7))
        | ~ r2_hidden(X6,a_3_1_yellow_6(sK6,sK7,X7))
        | ~ m1_subset_1(X7,u1_struct_0(sK7))
        | m1_subset_1(X6,u1_struct_0(sK6)) )
    | ~ spl22_35 ),
    inference(avatar_component_clause,[],[f427])).

fof(f429,plain,
    ( spl22_7
    | ~ spl22_24
    | spl22_4
    | ~ spl22_15
    | spl22_35
    | ~ spl22_34 ),
    inference(avatar_split_clause,[],[f425,f420,f427,f248,f178,f319,f202])).

fof(f319,plain,
    ( spl22_24
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_24])])).

fof(f420,plain,
    ( spl22_34
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,a_3_1_yellow_6(sK6,sK7,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK7))
        | k2_waybel_0(sK6,sK7,sK21(X0,sK6,sK7,X1)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_34])])).

fof(f425,plain,
    ( ! [X6,X7] :
        ( m1_subset_1(X6,u1_struct_0(sK6))
        | ~ m1_subset_1(sK21(X6,sK6,sK7,X7),u1_struct_0(sK7))
        | ~ l1_waybel_0(sK7,sK6)
        | v2_struct_0(sK7)
        | ~ l1_struct_0(sK6)
        | v2_struct_0(sK6)
        | ~ m1_subset_1(X7,u1_struct_0(sK7))
        | ~ r2_hidden(X6,a_3_1_yellow_6(sK6,sK7,X7)) )
    | ~ spl22_34 ),
    inference(superposition,[],[f145,f421])).

fof(f421,plain,
    ( ! [X0,X1] :
        ( k2_waybel_0(sK6,sK7,sK21(X0,sK6,sK7,X1)) = X0
        | ~ m1_subset_1(X1,u1_struct_0(sK7))
        | ~ r2_hidden(X0,a_3_1_yellow_6(sK6,sK7,X1)) )
    | ~ spl22_34 ),
    inference(avatar_component_clause,[],[f420])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

fof(f422,plain,
    ( ~ spl22_15
    | spl22_34
    | ~ spl22_16
    | spl22_7
    | ~ spl22_33 ),
    inference(avatar_split_clause,[],[f418,f415,f202,f252,f420,f248])).

fof(f415,plain,
    ( spl22_33
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,a_3_1_yellow_6(X1,sK7,X2))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | k2_waybel_0(X1,sK7,sK21(X0,X1,sK7,X2)) = X0
        | ~ l1_waybel_0(sK7,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_33])])).

fof(f418,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK6)
        | ~ v2_pre_topc(sK6)
        | ~ r2_hidden(X0,a_3_1_yellow_6(sK6,sK7,X1))
        | k2_waybel_0(sK6,sK7,sK21(X0,sK6,sK7,X1)) = X0
        | ~ l1_waybel_0(sK7,sK6)
        | ~ m1_subset_1(X1,u1_struct_0(sK7)) )
    | ~ spl22_33 ),
    inference(resolution,[],[f416,f94])).

fof(f416,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ r2_hidden(X0,a_3_1_yellow_6(X1,sK7,X2))
        | k2_waybel_0(X1,sK7,sK21(X0,X1,sK7,X2)) = X0
        | ~ l1_waybel_0(sK7,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK7)) )
    | ~ spl22_33 ),
    inference(avatar_component_clause,[],[f415])).

fof(f417,plain,
    ( spl22_4
    | ~ spl22_12
    | spl22_33 ),
    inference(avatar_split_clause,[],[f413,f415,f233,f178])).

fof(f413,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_3_1_yellow_6(X1,sK7,X2))
      | ~ m1_subset_1(X2,u1_struct_0(sK7))
      | ~ l1_waybel_0(sK7,X1)
      | k2_waybel_0(X1,sK7,sK21(X0,X1,sK7,X2)) = X0
      | ~ v4_orders_2(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f148,f97])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X2)
      | ~ r2_hidden(X0,a_3_1_yellow_6(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l1_waybel_0(X2,X1)
      | k2_waybel_0(X1,X2,sK21(X0,X1,X2,X3)) = X0
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f352,plain,
    ( spl22_7
    | ~ spl22_16
    | spl22_28 ),
    inference(avatar_split_clause,[],[f348,f350,f252,f202])).

fof(f348,plain,(
    ! [X0,X1] :
      ( m1_connsp_2(sK15(sK6,X0,X1),sK6,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
      | r2_hidden(X1,k2_pre_topc(sK6,X0))
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f123,f94])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_connsp_2(sK15(X0,X1,X2),X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(sK15(X0,X1,X2),X1)
                    & m1_connsp_2(sK15(X0,X1,X2),X0,X2) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X4,X1)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f69,f70])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X3,X1)
          & m1_connsp_2(X3,X0,X2) )
     => ( r1_xboole_0(sK15(X0,X1,X2),X1)
        & m1_connsp_2(sK15(X0,X1,X2),X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X3,X1)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X4,X1)
                      | ~ m1_connsp_2(X4,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X3,X1)
                      & m1_connsp_2(X3,X0,X2) ) )
                & ( ! [X3] :
                      ( ~ r1_xboole_0(X3,X1)
                      | ~ m1_connsp_2(X3,X0,X2) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X3,X1)
                    | ~ m1_connsp_2(X3,X0,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_connsp_2(X3,X0,X2)
                   => ~ r1_xboole_0(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_connsp_2)).

fof(f328,plain,(
    spl22_24 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl22_24 ),
    inference(resolution,[],[f326,f94])).

fof(f326,plain,
    ( ~ l1_pre_topc(sK6)
    | spl22_24 ),
    inference(resolution,[],[f321,f104])).

fof(f104,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f321,plain,
    ( ~ l1_struct_0(sK6)
    | spl22_24 ),
    inference(avatar_component_clause,[],[f319])).

fof(f310,plain,
    ( spl22_7
    | ~ spl22_16
    | spl22_23 ),
    inference(avatar_split_clause,[],[f306,f308,f252,f202])).

fof(f306,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(sK15(sK6,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK6))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
      | r2_hidden(X1,k2_pre_topc(sK6,X0))
      | ~ v2_pre_topc(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f124,f94])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_xboole_0(sK15(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f305,plain,
    ( spl22_22
    | ~ spl22_14
    | ~ spl22_21 ),
    inference(avatar_split_clause,[],[f299,f296,f244,f302])).

fof(f244,plain,
    ( spl22_14
  <=> m1_subset_1(k10_yellow_6(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_14])])).

fof(f296,plain,
    ( spl22_21
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | sP5(X0,sK6,sK7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_21])])).

fof(f299,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | sP4(sK7,sK6,k10_yellow_6(sK6,sK7))
    | ~ spl22_21 ),
    inference(resolution,[],[f297,f152])).

fof(f152,plain,(
    ! [X2,X1] :
      ( ~ sP5(k10_yellow_6(X1,X2),X1,X2)
      | sP4(X2,X1,k10_yellow_6(X1,X2)) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X1,X0)
      | k10_yellow_6(X1,X2) != X0
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( ( k10_yellow_6(X1,X2) = X0
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | k10_yellow_6(X1,X2) != X0 ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ( ( k10_yellow_6(X0,X1) = X2
          | ~ sP4(X1,X0,X2) )
        & ( sP4(X1,X0,X2)
          | k10_yellow_6(X0,X1) != X2 ) )
      | ~ sP5(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ( k10_yellow_6(X0,X1) = X2
      <=> sP4(X1,X0,X2) )
      | ~ sP5(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f297,plain,
    ( ! [X0] :
        ( sP5(X0,sK6,sK7)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) )
    | ~ spl22_21 ),
    inference(avatar_component_clause,[],[f296])).

fof(f298,plain,
    ( ~ spl22_15
    | spl22_21
    | ~ spl22_16
    | spl22_7
    | ~ spl22_19 ),
    inference(avatar_split_clause,[],[f294,f275,f202,f252,f296,f248])).

fof(f275,plain,
    ( spl22_19
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | sP5(X0,X1,sK7)
        | ~ l1_waybel_0(sK7,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_19])])).

fof(f294,plain,
    ( ! [X0] :
        ( v2_struct_0(sK6)
        | ~ v2_pre_topc(sK6)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
        | sP5(X0,sK6,sK7)
        | ~ l1_waybel_0(sK7,sK6) )
    | ~ spl22_19 ),
    inference(resolution,[],[f276,f94])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
        | sP5(X0,X1,sK7)
        | ~ l1_waybel_0(sK7,X1) )
    | ~ spl22_19 ),
    inference(avatar_component_clause,[],[f275])).

fof(f293,plain,(
    ~ spl22_18 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl22_18 ),
    inference(resolution,[],[f267,f100])).

fof(f267,plain,
    ( ! [X0] : ~ r2_hidden(X0,k10_yellow_6(sK6,sK7))
    | ~ spl22_18 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl22_18
  <=> ! [X0] : ~ r2_hidden(X0,k10_yellow_6(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_18])])).

fof(f277,plain,
    ( spl22_4
    | ~ spl22_12
    | spl22_19 ),
    inference(avatar_split_clause,[],[f273,f275,f233,f178])).

fof(f273,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_waybel_0(sK7,X1)
      | sP5(X0,X1,sK7)
      | ~ v4_orders_2(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f134,f97])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | sP5(X2,X0,X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP5(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f29,f48,f47])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f268,plain,
    ( spl22_17
    | spl22_18
    | ~ spl22_14 ),
    inference(avatar_split_clause,[],[f260,f244,f266,f263])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k10_yellow_6(sK6,sK7))
        | r2_hidden(X1,u1_struct_0(sK6))
        | ~ m1_subset_1(X1,u1_struct_0(sK6)) )
    | ~ spl22_14 ),
    inference(resolution,[],[f246,f169])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,X1) ) ),
    inference(resolution,[],[f146,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f246,plain,
    ( m1_subset_1(k10_yellow_6(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl22_14 ),
    inference(avatar_component_clause,[],[f244])).

fof(f259,plain,(
    spl22_15 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl22_15 ),
    inference(resolution,[],[f250,f98])).

fof(f98,plain,(
    l1_waybel_0(sK7,sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f250,plain,
    ( ~ l1_waybel_0(sK7,sK6)
    | spl22_15 ),
    inference(avatar_component_clause,[],[f248])).

fof(f257,plain,(
    spl22_16 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl22_16 ),
    inference(resolution,[],[f254,f93])).

fof(f93,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f254,plain,
    ( ~ v2_pre_topc(sK6)
    | spl22_16 ),
    inference(avatar_component_clause,[],[f252])).

fof(f255,plain,
    ( spl22_14
    | ~ spl22_15
    | ~ spl22_16
    | spl22_7
    | ~ spl22_13 ),
    inference(avatar_split_clause,[],[f242,f237,f202,f252,f248,f244])).

fof(f237,plain,
    ( spl22_13
  <=> ! [X0] :
        ( ~ l1_waybel_0(sK7,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_13])])).

fof(f242,plain,
    ( v2_struct_0(sK6)
    | ~ v2_pre_topc(sK6)
    | ~ l1_waybel_0(sK7,sK6)
    | m1_subset_1(k10_yellow_6(sK6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl22_13 ),
    inference(resolution,[],[f238,f94])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_waybel_0(sK7,X0)
        | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl22_13 ),
    inference(avatar_component_clause,[],[f237])).

fof(f241,plain,(
    spl22_12 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl22_12 ),
    inference(resolution,[],[f235,f96])).

fof(f96,plain,(
    v4_orders_2(sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f235,plain,
    ( ~ v4_orders_2(sK7)
    | spl22_12 ),
    inference(avatar_component_clause,[],[f233])).

fof(f239,plain,
    ( spl22_4
    | ~ spl22_12
    | spl22_13 ),
    inference(avatar_split_clause,[],[f231,f237,f233,f178])).

fof(f231,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK7,X0)
      | m1_subset_1(k10_yellow_6(X0,sK7),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(sK7)
      | v2_struct_0(sK7)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f139,f97])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f216,plain,
    ( spl22_9
    | spl22_4
    | ~ spl22_8 ),
    inference(avatar_split_clause,[],[f211,f206,f178,f213])).

fof(f206,plain,
    ( spl22_8
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK6)
        | sP3(sK6,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_8])])).

fof(f211,plain,
    ( v2_struct_0(sK7)
    | sP3(sK6,sK7)
    | ~ spl22_8 ),
    inference(resolution,[],[f207,f98])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(X0,sK6)
        | v2_struct_0(X0)
        | sP3(sK6,X0) )
    | ~ spl22_8 ),
    inference(avatar_component_clause,[],[f206])).

fof(f210,plain,(
    ~ spl22_7 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl22_7 ),
    inference(resolution,[],[f204,f92])).

fof(f92,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f54])).

fof(f204,plain,
    ( v2_struct_0(sK6)
    | ~ spl22_7 ),
    inference(avatar_component_clause,[],[f202])).

fof(f208,plain,
    ( spl22_7
    | spl22_8 ),
    inference(avatar_split_clause,[],[f200,f206,f202])).

fof(f200,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | sP3(sK6,X0)
      | v2_struct_0(sK6)
      | ~ l1_waybel_0(X0,sK6) ) ),
    inference(resolution,[],[f199,f94])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | v2_struct_0(X0)
      | sP3(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f121,f104])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | sP3(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f25,f45,f44])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f196,plain,(
    ~ spl22_4 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl22_4 ),
    inference(resolution,[],[f180,f95])).

fof(f95,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f54])).

fof(f180,plain,
    ( v2_struct_0(sK7)
    | ~ spl22_4 ),
    inference(avatar_component_clause,[],[f178])).

fof(f194,plain,(
    spl22_6 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl22_6 ),
    inference(resolution,[],[f191,f97])).

fof(f191,plain,
    ( ~ v7_waybel_0(sK7)
    | spl22_6 ),
    inference(avatar_component_clause,[],[f189])).

fof(f192,plain,
    ( spl22_5
    | ~ spl22_6
    | ~ spl22_3 ),
    inference(avatar_split_clause,[],[f183,f174,f189,f185])).

fof(f174,plain,
    ( spl22_3
  <=> sP1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_3])])).

fof(f183,plain,
    ( ~ v7_waybel_0(sK7)
    | sP0(sK7)
    | ~ spl22_3 ),
    inference(resolution,[],[f176,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v7_waybel_0(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v7_waybel_0(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f176,plain,
    ( sP1(sK7)
    | ~ spl22_3 ),
    inference(avatar_component_clause,[],[f174])).

fof(f181,plain,
    ( spl22_3
    | spl22_4 ),
    inference(avatar_split_clause,[],[f172,f178,f174])).

fof(f172,plain,
    ( v2_struct_0(sK7)
    | sP1(sK7) ),
    inference(resolution,[],[f171,f98])).

fof(f171,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK6)
      | v2_struct_0(X0)
      | sP1(X0) ) ),
    inference(resolution,[],[f170,f94])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | sP1(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f163,f104])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ l1_waybel_0(X0,X1)
      | sP1(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f103,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | sP1(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f42,f41])).

fof(f23,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_yellow_6)).

fof(f103,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f162,plain,
    ( ~ spl22_1
    | ~ spl22_2 ),
    inference(avatar_split_clause,[],[f151,f159,f155])).

fof(f151,plain,
    ( ~ r2_hidden(sK8,k2_pre_topc(sK6,a_3_1_yellow_6(sK6,sK7,sK9)))
    | ~ m1_subset_1(a_3_1_yellow_6(sK6,sK7,sK9),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK8,k2_pre_topc(sK6,X4))
      | a_3_1_yellow_6(sK6,sK7,sK9) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    inference(cnf_transformation,[],[f54])).

%------------------------------------------------------------------------------
