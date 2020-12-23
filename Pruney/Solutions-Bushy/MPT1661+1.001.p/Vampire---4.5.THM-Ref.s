%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1661+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 563 expanded)
%              Number of leaves         :   48 ( 273 expanded)
%              Depth                    :   13
%              Number of atoms          : 1238 (4906 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f729,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f88,f92,f96,f100,f105,f109,f113,f117,f121,f125,f135,f144,f156,f162,f174,f176,f178,f187,f205,f208,f361,f377,f408,f424,f454,f481,f548,f561,f657,f679,f686,f717,f724])).

fof(f724,plain,
    ( ~ spl10_10
    | ~ spl10_8
    | spl10_1
    | spl10_22 ),
    inference(avatar_split_clause,[],[f722,f185,f79,f107,f115])).

fof(f115,plain,
    ( spl10_10
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f107,plain,
    ( spl10_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f79,plain,
    ( spl10_1
  <=> v2_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f185,plain,
    ( spl10_22
  <=> r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f722,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl10_22 ),
    inference(resolution,[],[f186,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,sK5(X0,X1))
                    | ~ r1_orders_2(X0,X4,sK4(X0,X1))
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(sK5(X0,X1),X1)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ( r1_orders_2(X0,sK6(X0,X1,X5,X6),X6)
                        & r1_orders_2(X0,sK6(X0,X1,X5,X6),X5)
                        & r2_hidden(sK6(X0,X1,X5,X6),X1)
                        & m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f29,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                | ~ r1_orders_2(X0,X4,sK4(X0,X1))
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,sK4(X0,X1))
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(sK4(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,X4,sK5(X0,X1))
            | ~ r1_orders_2(X0,X4,sK4(X0,X1))
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,sK6(X0,X1,X5,X6),X6)
        & r1_orders_2(X0,sK6(X0,X1,X5,X6),X5)
        & r2_hidden(sK6(X0,X1,X5,X6),X1)
        & m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ? [X7] :
                          ( r1_orders_2(X0,X7,X6)
                          & r1_orders_2(X0,X7,X5)
                          & r2_hidden(X7,X1)
                          & m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X4,X3)
                                & r1_orders_2(X0,X4,X2)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_0)).

fof(f186,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl10_22 ),
    inference(avatar_component_clause,[],[f185])).

fof(f717,plain,
    ( ~ spl10_10
    | ~ spl10_8
    | spl10_1
    | spl10_21 ),
    inference(avatar_split_clause,[],[f715,f182,f79,f107,f115])).

fof(f182,plain,
    ( spl10_21
  <=> r2_hidden(sK4(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f715,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl10_21 ),
    inference(resolution,[],[f183,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f183,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),sK1)
    | spl10_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f686,plain,
    ( ~ spl10_10
    | ~ spl10_8
    | ~ spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_3
    | ~ spl10_4
    | spl10_101 ),
    inference(avatar_split_clause,[],[f684,f677,f90,f86,f98,f94,f79,f107,f115])).

fof(f94,plain,
    ( spl10_5
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f98,plain,
    ( spl10_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f86,plain,
    ( spl10_3
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f90,plain,
    ( spl10_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f677,plain,
    ( spl10_101
  <=> r2_hidden(sK6(sK0,sK1,sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_101])])).

fof(f684,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v2_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl10_101 ),
    inference(resolution,[],[f678,f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(sK6(X0,X1,X5,X6),X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f678,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3,sK2),sK1)
    | spl10_101 ),
    inference(avatar_component_clause,[],[f677])).

fof(f679,plain,
    ( ~ spl10_101
    | ~ spl10_76
    | ~ spl10_25
    | ~ spl10_97 ),
    inference(avatar_split_clause,[],[f670,f655,f203,f543,f677])).

fof(f543,plain,
    ( spl10_76
  <=> m1_subset_1(sK6(sK0,sK1,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f203,plain,
    ( spl10_25
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,k12_lattice3(sK0,sK2,sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f655,plain,
    ( spl10_97
  <=> r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),k12_lattice3(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f670,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3,sK2),u1_struct_0(sK0))
    | ~ r2_hidden(sK6(sK0,sK1,sK3,sK2),sK1)
    | ~ spl10_25
    | ~ spl10_97 ),
    inference(resolution,[],[f656,f204])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,k12_lattice3(sK0,sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f203])).

fof(f656,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),k12_lattice3(sK0,sK2,sK3))
    | ~ spl10_97 ),
    inference(avatar_component_clause,[],[f655])).

fof(f657,plain,
    ( ~ spl10_6
    | ~ spl10_4
    | ~ spl10_5
    | spl10_97
    | ~ spl10_52
    | ~ spl10_77 ),
    inference(avatar_split_clause,[],[f649,f546,f375,f655,f94,f90,f98])).

fof(f375,plain,
    ( spl10_52
  <=> ! [X4] :
        ( r1_orders_2(sK0,sK6(sK0,sK1,sK3,X4),sK3)
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f546,plain,
    ( spl10_77
  <=> ! [X3] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),X3)
        | r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),k12_lattice3(sK0,sK2,X3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f649,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),k12_lattice3(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_hidden(sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_52
    | ~ spl10_77 ),
    inference(resolution,[],[f547,f376])).

fof(f376,plain,
    ( ! [X4] :
        ( r1_orders_2(sK0,sK6(sK0,sK1,sK3,X4),sK3)
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f375])).

fof(f547,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),X3)
        | r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),k12_lattice3(sK0,sK2,X3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_77 ),
    inference(avatar_component_clause,[],[f546])).

fof(f561,plain,
    ( ~ spl10_10
    | ~ spl10_8
    | ~ spl10_1
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_3
    | ~ spl10_4
    | spl10_76 ),
    inference(avatar_split_clause,[],[f560,f543,f90,f86,f98,f94,f79,f107,f115])).

fof(f560,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v2_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl10_76 ),
    inference(resolution,[],[f544,f52])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( m1_subset_1(sK6(X0,X1,X5,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f544,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK3,sK2),u1_struct_0(sK0))
    | spl10_76 ),
    inference(avatar_component_clause,[],[f543])).

fof(f548,plain,
    ( ~ spl10_76
    | spl10_77
    | ~ spl10_6
    | ~ spl10_61
    | ~ spl10_65 ),
    inference(avatar_split_clause,[],[f532,f479,f452,f98,f546,f543])).

fof(f452,plain,
    ( spl10_61
  <=> r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f479,plain,
    ( spl10_65
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r1_orders_2(sK0,X0,k12_lattice3(sK0,X2,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f532,plain,
    ( ! [X3] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK3,sK2),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),k12_lattice3(sK0,sK2,X3)) )
    | ~ spl10_6
    | ~ spl10_61
    | ~ spl10_65 ),
    inference(resolution,[],[f499,f453])).

fof(f453,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),sK2)
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f452])).

fof(f499,plain,
    ( ! [X4,X5] :
        ( ~ r1_orders_2(sK0,X4,sK2)
        | ~ r1_orders_2(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_orders_2(sK0,X4,k12_lattice3(sK0,sK2,X5)) )
    | ~ spl10_6
    | ~ spl10_65 ),
    inference(resolution,[],[f480,f99])).

fof(f99,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f480,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,k12_lattice3(sK0,X2,X1))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2) )
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f479])).

fof(f481,plain,
    ( ~ spl10_12
    | ~ spl10_10
    | spl10_65
    | ~ spl10_11 ),
    inference(avatar_split_clause,[],[f477,f119,f479,f115,f123])).

fof(f123,plain,
    ( spl10_12
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f119,plain,
    ( spl10_11
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f477,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_orders_2(sK0,X0,k12_lattice3(sK0,X2,X1))
        | ~ v5_orders_2(sK0) )
    | ~ spl10_11 ),
    inference(resolution,[],[f128,f120])).

fof(f120,plain,
    ( v2_lattice3(sK0)
    | ~ spl10_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f128,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X5,k12_lattice3(X0,X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f75,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f75,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,k12_lattice3(X0,X1,X2))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK9(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK9(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK9(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f38,f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK9(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK9(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK9(X0,X1,X2,X3),X1)
        & m1_subset_1(sK9(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

fof(f454,plain,
    ( ~ spl10_6
    | spl10_61
    | ~ spl10_4
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f444,f422,f90,f452,f98])).

fof(f422,plain,
    ( spl10_58
  <=> ! [X4] :
        ( r1_orders_2(sK0,sK6(sK0,sK1,sK3,X4),X4)
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f444,plain,
    ( r1_orders_2(sK0,sK6(sK0,sK1,sK3,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_4
    | ~ spl10_58 ),
    inference(resolution,[],[f423,f91])).

fof(f91,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f423,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | r1_orders_2(sK0,sK6(sK0,sK1,sK3,X4),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f422])).

fof(f424,plain,
    ( ~ spl10_5
    | spl10_58
    | ~ spl10_3
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f411,f406,f86,f422,f94])).

fof(f406,plain,
    ( spl10_56
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,sK6(sK0,sK1,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f411,plain,
    ( ! [X4] :
        ( r1_orders_2(sK0,sK6(sK0,sK1,sK3,X4),X4)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl10_3
    | ~ spl10_56 ),
    inference(resolution,[],[f407,f87])).

fof(f87,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f407,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,sK6(sK0,sK1,X0,X1),X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f406])).

fof(f408,plain,
    ( ~ spl10_1
    | spl10_56
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f404,f115,f107,f406,f79])).

fof(f404,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_waybel_0(sK1,sK0)
        | ~ r2_hidden(X1,sK1)
        | r1_orders_2(sK0,sK6(sK0,sK1,X0,X1),X1) )
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(resolution,[],[f403,f108])).

fof(f108,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f403,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v2_waybel_0(X1,sK0)
        | ~ r2_hidden(X0,X1)
        | r1_orders_2(sK0,sK6(sK0,X1,X2,X0),X0) )
    | ~ spl10_10 ),
    inference(resolution,[],[f55,f116])).

fof(f116,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f55,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,sK6(X0,X1,X5,X6),X6) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f377,plain,
    ( ~ spl10_5
    | spl10_52
    | ~ spl10_3
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f364,f359,f86,f375,f94])).

fof(f359,plain,
    ( spl10_50
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,sK6(sK0,sK1,X0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f364,plain,
    ( ! [X4] :
        ( r1_orders_2(sK0,sK6(sK0,sK1,sK3,X4),sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1) )
    | ~ spl10_3
    | ~ spl10_50 ),
    inference(resolution,[],[f360,f87])).

fof(f360,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,sK6(sK0,sK1,X0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f359])).

fof(f361,plain,
    ( ~ spl10_1
    | spl10_50
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f357,f115,f107,f359,f79])).

fof(f357,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_waybel_0(sK1,sK0)
        | ~ r2_hidden(X1,sK1)
        | r1_orders_2(sK0,sK6(sK0,sK1,X0,X1),X0) )
    | ~ spl10_8
    | ~ spl10_10 ),
    inference(resolution,[],[f356,f108])).

fof(f356,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v2_waybel_0(X1,sK0)
        | ~ r2_hidden(X0,X1)
        | r1_orders_2(sK0,sK6(sK0,X1,X2,X0),X2) )
    | ~ spl10_10 ),
    inference(resolution,[],[f54,f116])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,sK6(X0,X1,X5,X6),X5) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f208,plain,
    ( ~ spl10_12
    | ~ spl10_11
    | ~ spl10_10
    | ~ spl10_6
    | ~ spl10_5
    | spl10_24 ),
    inference(avatar_split_clause,[],[f207,f200,f94,f98,f115,f119,f123])).

fof(f200,plain,
    ( spl10_24
  <=> m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f207,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl10_24 ),
    inference(resolution,[],[f201,f74])).

fof(f201,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl10_24 ),
    inference(avatar_component_clause,[],[f200])).

fof(f205,plain,
    ( ~ spl10_24
    | spl10_25
    | spl10_2
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f193,f133,f82,f203,f200])).

fof(f82,plain,
    ( spl10_2
  <=> r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f133,plain,
    ( spl10_13
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,k12_lattice3(sK0,sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k12_lattice3(sK0,sK2,sK3),u1_struct_0(sK0)) )
    | spl10_2
    | ~ spl10_13 ),
    inference(resolution,[],[f83,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f83,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f187,plain,
    ( ~ spl10_21
    | ~ spl10_22
    | ~ spl10_20
    | ~ spl10_15
    | ~ spl10_7
    | spl10_19 ),
    inference(avatar_split_clause,[],[f179,f169,f103,f151,f172,f185,f182])).

fof(f172,plain,
    ( spl10_20
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f151,plain,
    ( spl10_15
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f103,plain,
    ( spl10_7
  <=> ! [X5,X4] :
        ( r2_hidden(k12_lattice3(sK0,X4,X5),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f169,plain,
    ( spl10_19
  <=> r2_hidden(k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f179,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,sK1),sK1)
    | ~ r2_hidden(sK4(sK0,sK1),sK1)
    | ~ spl10_7
    | spl10_19 ),
    inference(resolution,[],[f170,f104])).

fof(f104,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k12_lattice3(sK0,X4,X5),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f170,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1)),sK1)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f178,plain,
    ( ~ spl10_10
    | ~ spl10_8
    | spl10_1
    | spl10_20 ),
    inference(avatar_split_clause,[],[f177,f172,f79,f107,f115])).

fof(f177,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl10_20 ),
    inference(resolution,[],[f173,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f173,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | spl10_20 ),
    inference(avatar_component_clause,[],[f172])).

fof(f176,plain,
    ( ~ spl10_12
    | ~ spl10_11
    | ~ spl10_10
    | ~ spl10_15
    | ~ spl10_20
    | spl10_18 ),
    inference(avatar_split_clause,[],[f175,f166,f172,f151,f115,f119,f123])).

fof(f166,plain,
    ( spl10_18
  <=> m1_subset_1(k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f175,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | spl10_18 ),
    inference(resolution,[],[f167,f74])).

fof(f167,plain,
    ( ~ m1_subset_1(k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1)),u1_struct_0(sK0))
    | spl10_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f174,plain,
    ( ~ spl10_12
    | ~ spl10_11
    | ~ spl10_10
    | ~ spl10_15
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_20
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f164,f154,f172,f169,f166,f151,f115,f119,f123])).

fof(f154,plain,
    ( spl10_16
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK5(sK0,sK1),X0),sK4(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,sK5(sK0,sK1),X0),sK1)
        | ~ m1_subset_1(k12_lattice3(sK0,sK5(sK0,sK1),X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f164,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1)),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl10_16 ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1)),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK5(sK0,sK1),sK4(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl10_16 ),
    inference(resolution,[],[f155,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f76,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK5(sK0,sK1),X0),sK4(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,sK5(sK0,sK1),X0),sK1)
        | ~ m1_subset_1(k12_lattice3(sK0,sK5(sK0,sK1),X0),u1_struct_0(sK0)) )
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f162,plain,
    ( ~ spl10_10
    | ~ spl10_8
    | spl10_1
    | spl10_15 ),
    inference(avatar_split_clause,[],[f161,f151,f79,f107,f115])).

fof(f161,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | spl10_15 ),
    inference(resolution,[],[f152,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f152,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | spl10_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f156,plain,
    ( ~ spl10_12
    | ~ spl10_11
    | ~ spl10_10
    | ~ spl10_15
    | spl10_16
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f145,f142,f154,f151,f115,f119,f123])).

fof(f142,plain,
    ( spl10_14
  <=> ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK4(sK0,sK1))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK5(sK0,sK1),X0),sK4(sK0,sK1))
        | ~ m1_subset_1(k12_lattice3(sK0,sK5(sK0,sK1),X0),u1_struct_0(sK0))
        | ~ r2_hidden(k12_lattice3(sK0,sK5(sK0,sK1),X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl10_14 ),
    inference(resolution,[],[f143,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f77,f74])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK5(sK0,sK1))
        | ~ r1_orders_2(sK0,X0,sK4(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f144,plain,
    ( ~ spl10_8
    | spl10_14
    | spl10_1
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f140,f115,f79,f142,f107])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK4(sK0,sK1))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,sK1)) )
    | spl10_1
    | ~ spl10_10 ),
    inference(resolution,[],[f139,f80])).

fof(f80,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( v2_waybel_0(X1,sK0)
        | ~ r1_orders_2(sK0,X0,sK4(sK0,X1))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_orders_2(sK0,X0,sK5(sK0,X1)) )
    | ~ spl10_10 ),
    inference(resolution,[],[f60,f116])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,sK5(X0,X1))
      | ~ r1_orders_2(X0,X4,sK4(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f135,plain,
    ( ~ spl10_8
    | spl10_13
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f130,f115,f111,f133,f107])).

fof(f111,plain,
    ( spl10_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK1) )
    | ~ spl10_9
    | ~ spl10_10 ),
    inference(resolution,[],[f129,f112])).

fof(f112,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f129,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X2,sK0)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl10_10 ),
    inference(resolution,[],[f61,f116])).

fof(f61,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK8(X0,X1),X1)
                & r1_orders_2(X0,sK7(X0,X1),sK8(X0,X1))
                & r2_hidden(sK7(X0,X1),X1)
                & m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK7(X0,X1),X3)
            & r2_hidden(sK7(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK7(X0,X1),X3)
          & r2_hidden(sK7(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r1_orders_2(X0,sK7(X0,X1),sK8(X0,X1))
        & r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f125,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f41,f123])).

fof(f41,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ( ~ r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1)
        & r2_hidden(sK3,sK1)
        & r2_hidden(sK2,sK1)
        & m1_subset_1(sK3,u1_struct_0(sK0))
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ v2_waybel_0(sK1,sK0) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(k12_lattice3(sK0,X4,X5),sK1)
              | ~ r2_hidden(X5,sK1)
              | ~ r2_hidden(X4,sK1)
              | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
          | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
      | v2_waybel_0(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v2_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k12_lattice3(sK0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(sK0)) )
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v2_waybel_0(X1,sK0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k12_lattice3(sK0,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | v2_waybel_0(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k12_lattice3(sK0,X2,X3),X1)
                  & r2_hidden(X3,X1)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ v2_waybel_0(X1,sK0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k12_lattice3(sK0,X4,X5),X1)
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
              | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
          | v2_waybel_0(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0) )
   => ( ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k12_lattice3(sK0,X2,X3),sK1)
                & r2_hidden(X3,sK1)
                & r2_hidden(X2,sK1)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ v2_waybel_0(sK1,sK0) )
      & ( ! [X4] :
            ( ! [X5] :
                ( r2_hidden(k12_lattice3(sK0,X4,X5),sK1)
                | ~ r2_hidden(X5,sK1)
                | ~ r2_hidden(X4,sK1)
                | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
            | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
        | v2_waybel_0(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(k12_lattice3(sK0,X2,X3),sK1)
            & r2_hidden(X3,sK1)
            & r2_hidden(X2,sK1)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r2_hidden(k12_lattice3(sK0,sK2,X3),sK1)
          & r2_hidden(X3,sK1)
          & r2_hidden(sK2,sK1)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ r2_hidden(k12_lattice3(sK0,sK2,X3),sK1)
        & r2_hidden(X3,sK1)
        & r2_hidden(sK2,sK1)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1)
      & r2_hidden(sK3,sK1)
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                    | ~ r2_hidden(X5,X1)
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    & r2_hidden(X3,X1)
                    & r2_hidden(X2,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0) )
           => ( v2_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( ( r2_hidden(X3,X1)
                          & r2_hidden(X2,X1) )
                       => r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_waybel_0)).

fof(f121,plain,(
    spl10_11 ),
    inference(avatar_split_clause,[],[f42,f119])).

fof(f42,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f117,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f43,f115])).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f113,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f44,f111])).

fof(f44,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f109,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f45,f107])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f105,plain,
    ( spl10_1
    | spl10_7 ),
    inference(avatar_split_clause,[],[f46,f103,f79])).

fof(f46,plain,(
    ! [X4,X5] :
      ( r2_hidden(k12_lattice3(sK0,X4,X5),sK1)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v2_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f100,plain,
    ( ~ spl10_1
    | spl10_6 ),
    inference(avatar_split_clause,[],[f47,f98,f79])).

fof(f47,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,
    ( ~ spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f48,f94,f79])).

fof(f48,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f49,f90,f79])).

fof(f49,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,
    ( ~ spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f50,f86,f79])).

fof(f50,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f84,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f51,f82,f79])).

fof(f51,plain,
    ( ~ r2_hidden(k12_lattice3(sK0,sK2,sK3),sK1)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

%------------------------------------------------------------------------------
