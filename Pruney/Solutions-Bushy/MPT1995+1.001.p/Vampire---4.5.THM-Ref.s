%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1995+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:02 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  265 ( 730 expanded)
%              Number of leaves         :   58 ( 332 expanded)
%              Depth                    :   18
%              Number of atoms          : 1797 (5518 expanded)
%              Number of equality atoms :    8 (  32 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f431,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f105,f110,f115,f120,f125,f130,f135,f140,f145,f150,f161,f168,f170,f177,f181,f200,f211,f226,f269,f279,f289,f319,f329,f337,f343,f349,f367,f396,f397,f398,f400,f406,f408,f417,f418,f420,f422,f428,f430])).

fof(f430,plain,
    ( ~ spl8_15
    | ~ spl8_34
    | spl8_14
    | ~ spl8_7
    | ~ spl8_5
    | spl8_1
    | spl8_39 ),
    inference(avatar_split_clause,[],[f429,f425,f89,f107,f117,f154,f385,f158])).

fof(f158,plain,
    ( spl8_15
  <=> m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f385,plain,
    ( spl8_34
  <=> m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f154,plain,
    ( spl8_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f117,plain,
    ( spl8_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f107,plain,
    ( spl8_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f89,plain,
    ( spl8_1
  <=> v5_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f425,plain,
    ( spl8_39
  <=> r2_hidden(k4_tarski(sK3(sK0,sK1),sK5(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f429,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl8_39 ),
    inference(resolution,[],[f427,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f72,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X1))
        & m1_subset_1(X2,u1_struct_0(X0))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k7_yellow_3(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_yellow_3)).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),sK5(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ( ~ r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1))),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),sK5(X0,X1)),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),sK4(X0,X1)),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ! [X7] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
                          | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f43,f46,f45,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                  & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),k11_lattice3(X0,X3,X4)),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),X4),X1)
                & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),X3),X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),k11_lattice3(X0,X3,X4)),X1)
              & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),X4),X1)
              & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),X3),X1)
              & m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ~ r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),k11_lattice3(X0,sK4(X0,X1),X4)),X1)
            & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),X4),X1)
            & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),sK4(X0,X1)),X1)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),k11_lattice3(X0,sK4(X0,X1),X4)),X1)
          & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),X4),X1)
          & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),sK4(X0,X1)),X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1))),X1)
        & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),sK4(X0,X1)),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ! [X7] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
                          | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ? [X4] :
                          ( ~ r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ! [X4] :
                          ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                          | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                        | ~ r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
         => ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r2_hidden(k7_yellow_3(X0,X0,X2,X4),X1)
                            & r2_hidden(k7_yellow_3(X0,X0,X2,X3),X1) )
                         => r2_hidden(k7_yellow_3(X0,X0,X2,k11_lattice3(X0,X3,X4)),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_waybel_7)).

fof(f427,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK1),sK5(sK0,sK1)),sK1)
    | spl8_39 ),
    inference(avatar_component_clause,[],[f425])).

fof(f428,plain,
    ( ~ spl8_15
    | ~ spl8_39
    | ~ spl8_20
    | spl8_35 ),
    inference(avatar_split_clause,[],[f423,f389,f209,f425,f158])).

fof(f209,plain,
    ( spl8_20
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | r2_hidden(X1,k6_waybel_4(sK0,X0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f389,plain,
    ( spl8_35
  <=> r2_hidden(sK5(sK0,sK1),k6_waybel_4(sK0,sK3(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f423,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK1),sK5(sK0,sK1)),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_20
    | spl8_35 ),
    inference(resolution,[],[f391,f210])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,k6_waybel_4(sK0,X0,sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f209])).

fof(f391,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k6_waybel_4(sK0,sK3(sK0,sK1),sK1))
    | spl8_35 ),
    inference(avatar_component_clause,[],[f389])).

fof(f422,plain,
    ( ~ spl8_15
    | ~ spl8_21
    | spl8_31 ),
    inference(avatar_split_clause,[],[f421,f373,f224,f158])).

fof(f224,plain,
    ( spl8_21
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f373,plain,
    ( spl8_31
  <=> v13_waybel_0(k6_waybel_4(sK0,sK3(sK0,sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f421,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_21
    | spl8_31 ),
    inference(resolution,[],[f375,f225])).

fof(f225,plain,
    ( ! [X0] :
        ( v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f224])).

fof(f375,plain,
    ( ~ v13_waybel_0(k6_waybel_4(sK0,sK3(sK0,sK1),sK1),sK0)
    | spl8_31 ),
    inference(avatar_component_clause,[],[f373])).

fof(f420,plain,
    ( ~ spl8_15
    | ~ spl8_4
    | spl8_32 ),
    inference(avatar_split_clause,[],[f419,f377,f103,f158])).

fof(f103,plain,
    ( spl8_4
  <=> ! [X3] :
        ( v2_waybel_0(k6_waybel_4(sK0,X3,sK1),sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f377,plain,
    ( spl8_32
  <=> v2_waybel_0(k6_waybel_4(sK0,sK3(sK0,sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f419,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_4
    | spl8_32 ),
    inference(resolution,[],[f379,f104])).

fof(f104,plain,
    ( ! [X3] :
        ( v2_waybel_0(k6_waybel_4(sK0,X3,sK1),sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f379,plain,
    ( ~ v2_waybel_0(k6_waybel_4(sK0,sK3(sK0,sK1),sK1),sK0)
    | spl8_32 ),
    inference(avatar_component_clause,[],[f377])).

fof(f418,plain,
    ( ~ spl8_7
    | ~ spl8_33
    | ~ spl8_34
    | spl8_36 ),
    inference(avatar_split_clause,[],[f413,f393,f385,f381,f117])).

fof(f381,plain,
    ( spl8_33
  <=> m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f393,plain,
    ( spl8_36
  <=> m1_subset_1(k11_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f413,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_36 ),
    inference(resolution,[],[f395,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

fof(f395,plain,
    ( ~ m1_subset_1(k11_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),u1_struct_0(sK0))
    | spl8_36 ),
    inference(avatar_component_clause,[],[f393])).

fof(f417,plain,
    ( spl8_38
    | ~ spl8_33
    | ~ spl8_34
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_24
    | spl8_36 ),
    inference(avatar_split_clause,[],[f412,f393,f287,f209,f166,f385,f381,f415])).

fof(f415,plain,
    ( spl8_38
  <=> ! [X0] :
        ( ~ v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ r2_hidden(sK5(sK0,sK1),k6_waybel_4(sK0,X0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,sK1),k6_waybel_4(sK0,X0,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f166,plain,
    ( spl8_16
  <=> ! [X0] :
        ( m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f287,plain,
    ( spl8_24
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k4_tarski(X2,k11_lattice3(sK0,X0,X1)),sK1)
        | ~ r2_hidden(X1,k6_waybel_4(sK0,X2,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ r2_hidden(X0,k6_waybel_4(sK0,X2,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f412,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ r2_hidden(sK4(sK0,sK1),k6_waybel_4(sK0,X0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK5(sK0,sK1),k6_waybel_4(sK0,X0,sK1)) )
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_24
    | spl8_36 ),
    inference(resolution,[],[f395,f297])).

fof(f297,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k11_lattice3(sK0,X2,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1)) )
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_24 ),
    inference(duplicate_literal_removal,[],[f296])).

fof(f296,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k11_lattice3(sK0,X2,X0),u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_24 ),
    inference(resolution,[],[f288,f216])).

fof(f216,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(resolution,[],[f210,f173])).

fof(f173,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k6_waybel_4(sK0,X2,sK1))
        | m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_16 ),
    inference(resolution,[],[f167,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f167,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f288,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X2,k11_lattice3(sK0,X0,X1)),sK1)
        | ~ r2_hidden(X1,k6_waybel_4(sK0,X2,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ r2_hidden(X0,k6_waybel_4(sK0,X2,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f287])).

fof(f408,plain,
    ( ~ spl8_15
    | ~ spl8_33
    | spl8_14
    | ~ spl8_7
    | ~ spl8_5
    | spl8_1
    | spl8_37 ),
    inference(avatar_split_clause,[],[f407,f403,f89,f107,f117,f154,f381,f158])).

fof(f403,plain,
    ( spl8_37
  <=> r2_hidden(k4_tarski(sK3(sK0,sK1),sK4(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f407,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl8_37 ),
    inference(resolution,[],[f405,f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f71,f87])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),sK4(X0,X1)),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f405,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK1),sK4(sK0,sK1)),sK1)
    | spl8_37 ),
    inference(avatar_component_clause,[],[f403])).

fof(f406,plain,
    ( ~ spl8_15
    | ~ spl8_37
    | ~ spl8_20
    | spl8_30 ),
    inference(avatar_split_clause,[],[f401,f369,f209,f403,f158])).

fof(f369,plain,
    ( spl8_30
  <=> r2_hidden(sK4(sK0,sK1),k6_waybel_4(sK0,sK3(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f401,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,sK1),sK4(sK0,sK1)),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_20
    | spl8_30 ),
    inference(resolution,[],[f371,f210])).

fof(f371,plain,
    ( ~ r2_hidden(sK4(sK0,sK1),k6_waybel_4(sK0,sK3(sK0,sK1),sK1))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f369])).

fof(f400,plain,
    ( ~ spl8_3
    | spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f399,f103,f93,f98])).

fof(f98,plain,
    ( spl8_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f93,plain,
    ( spl8_2
  <=> v2_waybel_0(k6_waybel_4(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f399,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f104,f95])).

fof(f95,plain,
    ( ~ v2_waybel_0(k6_waybel_4(sK0,sK2,sK1),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f398,plain,
    ( spl8_14
    | ~ spl8_7
    | spl8_1
    | spl8_33
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f162,f107,f381,f89,f117,f154])).

fof(f162,plain,
    ( m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f69,f109])).

fof(f109,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f397,plain,
    ( spl8_14
    | ~ spl8_7
    | spl8_1
    | spl8_34
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f163,f107,f385,f89,f117,f154])).

fof(f163,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f70,f109])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f396,plain,
    ( ~ spl8_30
    | ~ spl8_31
    | ~ spl8_32
    | ~ spl8_33
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_15
    | ~ spl8_36
    | spl8_14
    | ~ spl8_7
    | ~ spl8_5
    | spl8_1
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f302,f287,f89,f107,f117,f154,f393,f158,f389,f385,f381,f377,f373,f369])).

fof(f302,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k11_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,sK1),k6_waybel_4(sK0,sK3(sK0,sK1),sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_waybel_0(k6_waybel_4(sK0,sK3(sK0,sK1),sK1),sK0)
    | ~ v13_waybel_0(k6_waybel_4(sK0,sK3(sK0,sK1),sK1),sK0)
    | ~ r2_hidden(sK4(sK0,sK1),k6_waybel_4(sK0,sK3(sK0,sK1),sK1))
    | ~ spl8_24 ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,
    ( v5_waybel_7(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(k11_lattice3(sK0,sK4(sK0,sK1),sK5(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,sK1),k6_waybel_4(sK0,sK3(sK0,sK1),sK1))
    | ~ m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1),u1_struct_0(sK0))
    | ~ v2_waybel_0(k6_waybel_4(sK0,sK3(sK0,sK1),sK1),sK0)
    | ~ v13_waybel_0(k6_waybel_4(sK0,sK3(sK0,sK1),sK1),sK0)
    | ~ r2_hidden(sK4(sK0,sK1),k6_waybel_4(sK0,sK3(sK0,sK1),sK1))
    | ~ m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_24 ),
    inference(resolution,[],[f195,f288])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f73,f87])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k7_yellow_3(X0,X0,sK3(X0,X1),k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1))),X1)
      | v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f367,plain,
    ( ~ spl8_3
    | spl8_2
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f366,f347,f224,f198,f179,f175,f166,f93,f98])).

fof(f175,plain,
    ( spl8_17
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | r2_hidden(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),k6_waybel_4(sK0,X0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f179,plain,
    ( spl8_18
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | r2_hidden(sK6(sK0,k6_waybel_4(sK0,X1,sK1)),k6_waybel_4(sK0,X1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f198,plain,
    ( spl8_19
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f347,plain,
    ( spl8_29
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f366,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl8_2
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_29 ),
    inference(resolution,[],[f365,f95])).

fof(f365,plain,
    ( ! [X0] :
        ( v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_29 ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,
    ( ! [X0] :
        ( v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_29 ),
    inference(resolution,[],[f363,f225])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(resolution,[],[f361,f167])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(resolution,[],[f357,f185])).

fof(f185,plain,
    ( ! [X0] :
        ( m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(resolution,[],[f180,f173])).

fof(f180,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(sK0,k6_waybel_4(sK0,X1,sK1)),k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f179])).

fof(f357,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl8_16
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(resolution,[],[f353,f183])).

fof(f183,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl8_16
    | ~ spl8_17 ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_17 ),
    inference(resolution,[],[f176,f173])).

fof(f176,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),k6_waybel_4(sK0,X0,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(duplicate_literal_removal,[],[f352])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl8_17
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(resolution,[],[f351,f205])).

fof(f205,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK6(sK0,k6_waybel_4(sK0,X1,sK1))),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0) )
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(X1,sK6(sK0,k6_waybel_4(sK0,X1,sK1))),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_18
    | ~ spl8_19 ),
    inference(resolution,[],[f199,f180])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f198])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(duplicate_literal_removal,[],[f350])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl8_17
    | ~ spl8_19
    | ~ spl8_29 ),
    inference(resolution,[],[f348,f206])).

fof(f206,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(resolution,[],[f199,f176])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k4_tarski(X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f347])).

fof(f349,plain,
    ( spl8_14
    | ~ spl8_7
    | spl8_29
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f345,f341,f347,f117,f154])).

fof(f341,plain,
    ( spl8_28
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_28 ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_28 ),
    inference(superposition,[],[f342,f87])).

fof(f342,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f341])).

fof(f343,plain,
    ( spl8_14
    | ~ spl8_7
    | spl8_28
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f339,f335,f341,f117,f154])).

fof(f335,plain,
    ( spl8_27
  <=> ! [X2] :
        ( ~ v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,sK7(sK0,k6_waybel_4(sK0,X2,sK1))),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,sK6(sK0,k6_waybel_4(sK0,X2,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f339,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_27 ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_27 ),
    inference(superposition,[],[f336,f87])).

fof(f336,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,sK7(sK0,k6_waybel_4(sK0,X2,sK1))),sK1)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,sK6(sK0,k6_waybel_4(sK0,X2,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f335])).

fof(f337,plain,
    ( ~ spl8_7
    | spl8_27
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f332,f327,f335,f117])).

fof(f327,plain,
    ( spl8_26
  <=> ! [X0] :
        ( ~ m1_subset_1(k11_lattice3(sK0,sK6(sK0,k6_waybel_4(sK0,X0,sK1)),sK7(sK0,k6_waybel_4(sK0,X0,sK1))),u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f332,plain,
    ( ! [X2] :
        ( ~ v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,sK6(sK0,k6_waybel_4(sK0,X2,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,sK7(sK0,k6_waybel_4(sK0,X2,sK1))),sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_26 ),
    inference(duplicate_literal_removal,[],[f331])).

fof(f331,plain,
    ( ! [X2] :
        ( ~ v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,sK6(sK0,k6_waybel_4(sK0,X2,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X2,sK7(sK0,k6_waybel_4(sK0,X2,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X2,sK1)),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f328,f85])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k11_lattice3(sK0,sK6(sK0,k6_waybel_4(sK0,X0,sK1)),sK7(sK0,k6_waybel_4(sK0,X0,sK1))),u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f327])).

fof(f329,plain,
    ( ~ spl8_11
    | ~ spl8_8
    | ~ spl8_7
    | spl8_26
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f325,f317,f209,f327,f117,f122,f137])).

fof(f137,plain,
    ( spl8_11
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f122,plain,
    ( spl8_8
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f317,plain,
    ( spl8_25
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X1),sK1)
        | ~ m1_subset_1(k11_lattice3(sK0,X2,X1),u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,k11_lattice3(sK0,X2,X1)),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X2),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f325,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k11_lattice3(sK0,sK6(sK0,k6_waybel_4(sK0,X0,sK1)),sK7(sK0,k6_waybel_4(sK0,X0,sK1))),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k11_lattice3(sK0,sK6(sK0,k6_waybel_4(sK0,X0,sK1)),sK7(sK0,k6_waybel_4(sK0,X0,sK1))),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK7(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,sK6(sK0,k6_waybel_4(sK0,X0,sK1))),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,k6_waybel_4(sK0,X0,sK1)),u1_struct_0(sK0)) )
    | ~ spl8_20
    | ~ spl8_25 ),
    inference(resolution,[],[f318,f258])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,k11_lattice3(X0,sK6(X0,k6_waybel_4(sK0,X1,sK1)),sK7(X0,k6_waybel_4(sK0,X1,sK1)))),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),X0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X1,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ m1_subset_1(sK7(X0,k6_waybel_4(sK0,X1,sK1)),u1_struct_0(X0))
        | ~ m1_subset_1(sK6(X0,k6_waybel_4(sK0,X1,sK1)),u1_struct_0(X0)) )
    | ~ spl8_20 ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X1,k11_lattice3(X0,sK6(X0,k6_waybel_4(sK0,X1,sK1)),sK7(X0,k6_waybel_4(sK0,X1,sK1)))),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),X0)
        | ~ m1_subset_1(k6_waybel_4(sK0,X1,sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),X0)
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0)
        | ~ m1_subset_1(sK7(X0,k6_waybel_4(sK0,X1,sK1)),u1_struct_0(X0))
        | ~ m1_subset_1(sK6(X0,k6_waybel_4(sK0,X1,sK1)),u1_struct_0(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_lattice3(X0)
        | ~ v5_orders_2(X0) )
    | ~ spl8_20 ),
    inference(superposition,[],[f214,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f214,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(k4_tarski(X4,k12_lattice3(X5,sK6(X5,k6_waybel_4(sK0,X4,sK1)),sK7(X5,k6_waybel_4(sK0,X4,sK1)))),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v2_waybel_0(k6_waybel_4(sK0,X4,sK1),X5)
        | ~ m1_subset_1(k6_waybel_4(sK0,X4,sK1),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X4,sK1),X5)
        | ~ l1_orders_2(X5)
        | ~ v2_lattice3(X5)
        | ~ v5_orders_2(X5) )
    | ~ spl8_20 ),
    inference(resolution,[],[f210,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k12_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
      | v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ~ r2_hidden(k12_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
                & r2_hidden(sK7(X0,X1),X1)
                & r2_hidden(sK6(X0,X1),X1)
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f49,f51,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k12_lattice3(X0,sK6(X0,X1),X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK6(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k12_lattice3(X0,sK6(X0,X1),X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(sK6(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k12_lattice3(X0,sK6(X0,X1),sK7(X0,X1)),X1)
        & r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_waybel_0)).

fof(f318,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X0,k11_lattice3(sK0,X2,X1)),sK1)
        | ~ m1_subset_1(k11_lattice3(sK0,X2,X1),u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X1),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X2),sK1) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f317])).

fof(f319,plain,
    ( spl8_14
    | ~ spl8_7
    | ~ spl8_1
    | spl8_25
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f315,f107,f317,f89,f117,f154])).

fof(f315,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X1),sK1)
        | ~ r2_hidden(k7_yellow_3(sK0,sK0,X0,X2),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_waybel_7(sK1,sK0)
        | r2_hidden(k4_tarski(X0,k11_lattice3(sK0,X2,X1)),sK1)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k11_lattice3(sK0,X2,X1),u1_struct_0(sK0)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f294,f109])).

fof(f294,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X3),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X2),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_7(X4,X0)
      | r2_hidden(k4_tarski(X1,k11_lattice3(X0,X2,X3)),X4)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,X2,X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X1,k11_lattice3(X0,X2,X3)),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X3),X4)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X1,X2),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_waybel_7(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k11_lattice3(X0,X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f67,f87])).

fof(f67,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( r2_hidden(k7_yellow_3(X0,X0,X5,k11_lattice3(X0,X6,X7)),X1)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X7),X1)
      | ~ r2_hidden(k7_yellow_3(X0,X0,X5,X6),X1)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v5_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f289,plain,
    ( ~ spl8_11
    | ~ spl8_8
    | ~ spl8_7
    | spl8_24
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f283,f277,f287,f117,f122,f137])).

fof(f277,plain,
    ( spl8_23
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f283,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X2,k11_lattice3(sK0,X0,X1)),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k6_waybel_4(sK0,X2,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k6_waybel_4(sK0,X2,sK1))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_23 ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X2,k11_lattice3(sK0,X0,X1)),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k6_waybel_4(sK0,X2,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k6_waybel_4(sK0,X2,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_23 ),
    inference(superposition,[],[f278,f84])).

fof(f278,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1)) )
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f277])).

fof(f279,plain,
    ( ~ spl8_11
    | ~ spl8_8
    | ~ spl8_7
    | spl8_23
    | ~ spl8_16
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f275,f198,f166,f277,f117,f122,f137])).

fof(f275,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_19 ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | r2_hidden(k4_tarski(X1,k12_lattice3(sK0,X0,X2)),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_16
    | ~ spl8_19 ),
    inference(resolution,[],[f250,f167])).

fof(f250,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ m1_subset_1(k6_waybel_4(sK0,X3,sK1),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ r2_hidden(X4,k6_waybel_4(sK0,X3,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(X5))
        | ~ m1_subset_1(X4,u1_struct_0(X5))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X3,sK1),X5)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X3,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X3,sK1),X5)
        | ~ l1_orders_2(X5)
        | ~ v2_lattice3(X5)
        | ~ v5_orders_2(X5)
        | r2_hidden(k4_tarski(X3,k12_lattice3(X5,X4,X2)),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_19 ),
    inference(resolution,[],[f74,f199])).

fof(f74,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f269,plain,
    ( ~ spl8_11
    | ~ spl8_8
    | ~ spl8_7
    | spl8_22
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f265,f166,f267,f117,f122,f137])).

fof(f267,plain,
    ( spl8_22
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k12_lattice3(sK0,X0,X2),u1_struct_0(sK0))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f265,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | m1_subset_1(k12_lattice3(sK0,X0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_16 ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ r2_hidden(X2,k6_waybel_4(sK0,X1,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | m1_subset_1(k12_lattice3(sK0,X0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl8_16 ),
    inference(resolution,[],[f251,f167])).

fof(f251,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ m1_subset_1(k6_waybel_4(sK0,X7,sK1),k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r2_hidden(X8,k6_waybel_4(sK0,X7,sK1))
        | ~ m1_subset_1(X6,u1_struct_0(X9))
        | ~ m1_subset_1(X8,u1_struct_0(X9))
        | ~ v2_waybel_0(k6_waybel_4(sK0,X7,sK1),X9)
        | ~ r2_hidden(X6,k6_waybel_4(sK0,X7,sK1))
        | ~ v13_waybel_0(k6_waybel_4(sK0,X7,sK1),X9)
        | ~ l1_orders_2(X9)
        | ~ v2_lattice3(X9)
        | ~ v5_orders_2(X9)
        | m1_subset_1(k12_lattice3(X9,X8,X6),u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl8_16 ),
    inference(resolution,[],[f74,f173])).

fof(f226,plain,
    ( ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_10
    | ~ spl8_9
    | ~ spl8_7
    | ~ spl8_6
    | spl8_21
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f222,f107,f224,f112,f117,f127,f132,f137,f142,f147])).

fof(f147,plain,
    ( spl8_13
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f142,plain,
    ( spl8_12
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f132,plain,
    ( spl8_10
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f127,plain,
    ( spl8_9
  <=> v1_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f112,plain,
    ( spl8_6
  <=> v5_waybel_4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v5_waybel_4(sK1,sK0)
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f83,f109])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v13_waybel_0(k6_waybel_4(X0,X2,X1),X0)
      | ~ v5_waybel_4(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v13_waybel_0(k6_waybel_4(X0,X2,X1),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v5_waybel_4(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v13_waybel_0(k6_waybel_4(X0,X2,X1),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ v5_waybel_4(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v5_waybel_4(X1,X0)
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => v13_waybel_0(k6_waybel_4(X0,X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_waybel_7)).

fof(f211,plain,
    ( ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_9
    | ~ spl8_7
    | spl8_20
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f207,f107,f209,f117,f127,f137,f142,f147])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,k6_waybel_4(sK0,X0,sK1))
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f81,f109])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(X0,k6_waybel_4(X1,X3,X2))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( ( r2_hidden(X0,k6_waybel_4(X1,X3,X2))
                  | ~ r2_hidden(k4_tarski(X3,X0),X2) )
                & ( r2_hidden(k4_tarski(X3,X0),X2)
                  | ~ r2_hidden(X0,k6_waybel_4(X1,X3,X2)) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r2_hidden(X0,k6_waybel_4(X1,X3,X2))
              <=> r2_hidden(k4_tarski(X3,X0),X2) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r2_hidden(X0,k6_waybel_4(X1,X3,X2))
              <=> r2_hidden(k4_tarski(X3,X0),X2) )
              | ~ m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_orders_2(X1)
        & v1_lattice3(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X0,k6_waybel_4(X1,X3,X2))
              <=> r2_hidden(k4_tarski(X3,X0),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_waybel_4)).

fof(f200,plain,
    ( ~ spl8_13
    | ~ spl8_12
    | ~ spl8_11
    | ~ spl8_9
    | ~ spl8_7
    | spl8_19
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f196,f107,f198,f117,f127,f137,f142,f147])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k6_waybel_4(sK0,X1,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ l1_orders_2(sK0)
        | ~ v1_lattice3(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f80,f109])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
      | ~ r2_hidden(X0,k6_waybel_4(X1,X3,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(k4_tarski(X3,X0),X2)
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f181,plain,
    ( ~ spl8_11
    | ~ spl8_8
    | ~ spl8_7
    | spl8_18
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f172,f166,f179,f117,f122,f137])).

fof(f172,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,k6_waybel_4(sK0,X1,sK1)),k6_waybel_4(sK0,X1,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X1,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_16 ),
    inference(resolution,[],[f167,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK6(X0,X1),X1)
      | v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f177,plain,
    ( ~ spl8_11
    | ~ spl8_8
    | ~ spl8_7
    | spl8_17
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f171,f166,f175,f117,f122,f137])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK7(sK0,k6_waybel_4(sK0,X0,sK1)),k6_waybel_4(sK0,X0,sK1))
        | v2_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ v13_waybel_0(k6_waybel_4(sK0,X0,sK1),sK0)
        | ~ l1_orders_2(sK0)
        | ~ v2_lattice3(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl8_16 ),
    inference(resolution,[],[f167,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK7(X0,X1),X1)
      | v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f170,plain,
    ( ~ spl8_7
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f169,f154,f122,f117])).

fof(f169,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl8_14 ),
    inference(resolution,[],[f156,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f156,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f168,plain,
    ( spl8_14
    | ~ spl8_7
    | spl8_16
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f164,f107,f166,f117,f154])).

fof(f164,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_waybel_4(sK0,X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f82,f109])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(k6_waybel_4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k6_waybel_4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k6_waybel_4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_waybel_4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_waybel_4)).

fof(f161,plain,
    ( spl8_14
    | ~ spl8_7
    | spl8_1
    | spl8_15
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f152,f107,f158,f89,f117,f154])).

fof(f152,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | v5_waybel_7(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f68,f109])).

% (6849)Refutation not found, incomplete strategy% (6849)------------------------------
% (6849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6849)Termination reason: Refutation not found, incomplete strategy

% (6849)Memory used [KB]: 1791
% (6849)Time elapsed: 0.194 s
% (6849)------------------------------
% (6849)------------------------------
fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v5_waybel_7(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f150,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f54,f147])).

fof(f54,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ( ~ v2_waybel_0(k6_waybel_4(sK0,sK2,sK1),sK0)
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ v5_waybel_7(sK1,sK0) )
    & ( ! [X3] :
          ( v2_waybel_0(k6_waybel_4(sK0,X3,sK1),sK0)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | v5_waybel_7(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    & v5_waybel_4(sK1,sK0)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_7(X1,X0) )
            & ( ! [X3] :
                  ( v2_waybel_0(k6_waybel_4(X0,X3,X1),X0)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | v5_waybel_7(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
            & v5_waybel_4(X1,X0) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ v2_waybel_0(k6_waybel_4(sK0,X2,X1),sK0)
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v5_waybel_7(X1,sK0) )
          & ( ! [X3] :
                ( v2_waybel_0(k6_waybel_4(sK0,X3,X1),sK0)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            | v5_waybel_7(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
          & v5_waybel_4(X1,sK0) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ~ v2_waybel_0(k6_waybel_4(sK0,X2,X1),sK0)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ v5_waybel_7(X1,sK0) )
        & ( ! [X3] :
              ( v2_waybel_0(k6_waybel_4(sK0,X3,X1),sK0)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          | v5_waybel_7(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
        & v5_waybel_4(X1,sK0) )
   => ( ( ? [X2] :
            ( ~ v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ v5_waybel_7(sK1,sK0) )
      & ( ! [X3] :
            ( v2_waybel_0(k6_waybel_4(sK0,X3,sK1),sK0)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        | v5_waybel_7(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
      & v5_waybel_4(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ~ v2_waybel_0(k6_waybel_4(sK0,X2,sK1),sK0)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ v2_waybel_0(k6_waybel_4(sK0,sK2,sK1),sK0)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X3] :
                ( v2_waybel_0(k6_waybel_4(X0,X3,X1),X0)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v5_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v5_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_waybel_7(X1,X0)
          <~> ! [X2] :
                ( v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_waybel_7(X1,X0)
          <~> ! [X2] :
                ( v2_waybel_0(k6_waybel_4(X0,X2,X1),X0)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
          & v5_waybel_4(X1,X0) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
              & v5_waybel_4(X1,X0) )
           => ( v5_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => v2_waybel_0(k6_waybel_4(X0,X2,X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
            & v5_waybel_4(X1,X0) )
         => ( v5_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => v2_waybel_0(k6_waybel_4(X0,X2,X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_waybel_7)).

fof(f145,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f55,f142])).

fof(f55,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f140,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f56,f137])).

fof(f56,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f135,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f57,f132])).

fof(f57,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f130,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f58,f127])).

fof(f58,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f59,f122])).

fof(f59,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f60,f117])).

fof(f60,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f115,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f61,f112])).

fof(f61,plain,(
    v5_waybel_4(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f110,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f62,f107])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,
    ( spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f63,f103,f89])).

fof(f63,plain,(
    ! [X3] :
      ( v2_waybel_0(k6_waybel_4(sK0,X3,sK1),sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v5_waybel_7(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f64,f98,f89])).

fof(f64,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f65,f93,f89])).

fof(f65,plain,
    ( ~ v2_waybel_0(k6_waybel_4(sK0,sK2,sK1),sK0)
    | ~ v5_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

%------------------------------------------------------------------------------
