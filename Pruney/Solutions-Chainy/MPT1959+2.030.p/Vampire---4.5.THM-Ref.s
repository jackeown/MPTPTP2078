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
% DateTime   : Thu Dec  3 13:22:55 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 357 expanded)
%              Number of leaves         :   41 ( 125 expanded)
%              Depth                    :   17
%              Number of atoms          :  767 (2081 expanded)
%              Number of equality atoms :   41 (  62 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f504,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f142,f147,f152,f161,f163,f193,f249,f270,f341,f350,f363,f379,f403,f442,f470,f502])).

fof(f502,plain,
    ( ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_17
    | spl8_28
    | ~ spl8_30 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_17
    | spl8_28
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f499,f474])).

fof(f474,plain,
    ( ~ r1_orders_2(sK0,k3_yellow_0(sK0),sK6(u1_struct_0(sK0),sK1))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16
    | spl8_28
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f131,f141,f159,f242,f151,f441,f469,f81])).

fof(f81,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).

fof(f52,plain,(
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
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK2(X0,X1),X3)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f469,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f467])).

fof(f467,plain,
    ( spl8_30
  <=> m1_subset_1(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f441,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK0),sK1),sK1)
    | spl8_28 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl8_28
  <=> r2_hidden(sK6(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f151,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f242,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl8_16
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f159,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl8_10
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f141,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl8_6
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f131,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f499,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK6(u1_struct_0(sK0),sK1))
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_17
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f469,f293])).

fof(f293,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_12
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f261,f292])).

fof(f292,plain,
    ( ! [X5] :
        ( r2_lattice3(sK0,k1_xboole_0,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f289,f264])).

fof(f264,plain,
    ( k1_xboole_0 = k2_subset_1(k1_xboole_0)
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f79,f170,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f170,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_subset_1(k1_xboole_0))
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f146,f79,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f146,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f289,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_subset_1(k1_xboole_0),X5) )
    | ~ spl8_4
    | ~ spl8_7 ),
    inference(resolution,[],[f196,f170])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl8_4 ),
    inference(resolution,[],[f94,f131])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f261,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f260,f131])).

fof(f260,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_12
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f257,f192])).

fof(f192,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl8_12
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f257,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_17 ),
    inference(superposition,[],[f112,f248])).

fof(f248,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl8_17
  <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f108,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_lattice3(X0,X1,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_yellow_0(X0,X1) != X2
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_lattice3(X0,X1,sK4(X0,X1,X2))
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_lattice3(X0,X1,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f470,plain,
    ( spl8_30
    | ~ spl8_8
    | spl8_13 ),
    inference(avatar_split_clause,[],[f370,f210,f149,f467])).

fof(f210,plain,
    ( spl8_13
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f370,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl8_8
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f151,f211,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f211,plain,
    ( u1_struct_0(sK0) != sK1
    | spl8_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f442,plain,
    ( ~ spl8_28
    | ~ spl8_8
    | spl8_13 ),
    inference(avatar_split_clause,[],[f369,f210,f149,f439])).

fof(f369,plain,
    ( ~ r2_hidden(sK6(u1_struct_0(sK0),sK1),sK1)
    | ~ spl8_8
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f151,f211,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f403,plain,
    ( spl8_16
    | ~ spl8_4
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f335,f246,f129,f240])).

fof(f335,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl8_4
    | ~ spl8_17 ),
    inference(subsumption_resolution,[],[f259,f131])).

fof(f259,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl8_17 ),
    inference(superposition,[],[f97,f248])).

fof(f379,plain,
    ( spl8_10
    | spl8_5
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f353,f176,f134,f158])).

fof(f134,plain,
    ( spl8_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f176,plain,
    ( spl8_11
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f353,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | spl8_5
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f136,f177,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f177,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f176])).

fof(f136,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f363,plain,
    ( ~ spl8_8
    | ~ spl8_13
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_13
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f356,f351])).

fof(f351,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f349,f110])).

fof(f110,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f349,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl8_22
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f356,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl8_8
    | ~ spl8_13 ),
    inference(superposition,[],[f151,f212])).

fof(f212,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f350,plain,
    ( spl8_22
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f344,f210,f154,f347])).

fof(f154,plain,
    ( spl8_9
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f344,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(forward_demodulation,[],[f156,f212])).

fof(f156,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f154])).

fof(f341,plain,
    ( u1_struct_0(sK0) != sK1
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f270,plain,
    ( spl8_9
    | spl8_13
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f173,f149,f210,f154])).

fof(f173,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_8 ),
    inference(resolution,[],[f103,f151])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f249,plain,
    ( spl8_17
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f164,f129,f246])).

fof(f164,plain,
    ( k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f131,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f193,plain,
    ( spl8_12
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f181,f129,f124,f119,f114,f190])).

fof(f114,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f119,plain,
    ( spl8_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f124,plain,
    ( spl8_3
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f181,plain,
    ( r1_yellow_0(sK0,k1_xboole_0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f96])).

fof(f96,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r1_yellow_0(X0,k1_xboole_0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f126,plain,
    ( v1_yellow_0(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f121,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f116,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f163,plain,
    ( ~ spl8_9
    | spl8_10 ),
    inference(avatar_split_clause,[],[f162,f158,f154])).

fof(f162,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl8_10 ),
    inference(subsumption_resolution,[],[f77,f160])).

fof(f160,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f158])).

fof(f77,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f161,plain,
    ( spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f76,f158,f154])).

fof(f76,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f152,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f75,f149])).

fof(f75,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f147,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f78,f144])).

fof(f78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f142,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f74,f139])).

fof(f74,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f137,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f73,f134])).

fof(f73,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f132,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f72,f129])).

fof(f72,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f127,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f71,f124])).

fof(f71,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f70,f119])).

fof(f70,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f117,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f69,f114])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:31:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (32433)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.46  % (32441)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.49  % (32423)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (32434)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (32444)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (32426)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (32439)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.50  % (32443)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.50  % (32436)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (32427)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (32430)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (32438)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.51  % (32425)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (32422)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (32431)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (32428)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (32422)Refutation not found, incomplete strategy% (32422)------------------------------
% 0.22/0.51  % (32422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32422)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (32422)Memory used [KB]: 10618
% 0.22/0.51  % (32422)Time elapsed: 0.107 s
% 0.22/0.51  % (32422)------------------------------
% 0.22/0.51  % (32422)------------------------------
% 0.22/0.51  % (32435)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (32429)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (32446)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (32429)Refutation not found, incomplete strategy% (32429)------------------------------
% 0.22/0.52  % (32429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32429)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32429)Memory used [KB]: 1663
% 0.22/0.52  % (32429)Time elapsed: 0.105 s
% 0.22/0.52  % (32429)------------------------------
% 0.22/0.52  % (32429)------------------------------
% 0.22/0.52  % (32432)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (32424)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (32442)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (32437)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (32445)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (32447)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.48/0.56  % (32440)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.48/0.56  % (32445)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.57/0.56  % SZS output start Proof for theBenchmark
% 1.57/0.56  fof(f504,plain,(
% 1.57/0.56    $false),
% 1.57/0.56    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f142,f147,f152,f161,f163,f193,f249,f270,f341,f350,f363,f379,f403,f442,f470,f502])).
% 1.57/0.56  fof(f502,plain,(
% 1.57/0.56    ~spl8_4 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_16 | ~spl8_17 | spl8_28 | ~spl8_30),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f501])).
% 1.57/0.56  fof(f501,plain,(
% 1.57/0.56    $false | (~spl8_4 | ~spl8_6 | ~spl8_7 | ~spl8_8 | ~spl8_10 | ~spl8_12 | ~spl8_16 | ~spl8_17 | spl8_28 | ~spl8_30)),
% 1.57/0.56    inference(subsumption_resolution,[],[f499,f474])).
% 1.57/0.56  fof(f474,plain,(
% 1.57/0.56    ~r1_orders_2(sK0,k3_yellow_0(sK0),sK6(u1_struct_0(sK0),sK1)) | (~spl8_4 | ~spl8_6 | ~spl8_8 | ~spl8_10 | ~spl8_16 | spl8_28 | ~spl8_30)),
% 1.57/0.56    inference(unit_resulting_resolution,[],[f131,f141,f159,f242,f151,f441,f469,f81])).
% 1.57/0.56  fof(f81,plain,(
% 1.57/0.56    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f54])).
% 1.57/0.56  fof(f54,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f51,f53,f52])).
% 1.57/0.57  fof(f52,plain,(
% 1.57/0.57    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f53,plain,(
% 1.57/0.57    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f51,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(rectify,[],[f50])).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(nnf_transformation,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(flattening,[],[f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,axiom,(
% 1.57/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.57/0.57  fof(f469,plain,(
% 1.57/0.57    m1_subset_1(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl8_30),
% 1.57/0.57    inference(avatar_component_clause,[],[f467])).
% 1.57/0.57  fof(f467,plain,(
% 1.57/0.57    spl8_30 <=> m1_subset_1(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 1.57/0.57  fof(f441,plain,(
% 1.57/0.57    ~r2_hidden(sK6(u1_struct_0(sK0),sK1),sK1) | spl8_28),
% 1.57/0.57    inference(avatar_component_clause,[],[f439])).
% 1.57/0.57  fof(f439,plain,(
% 1.57/0.57    spl8_28 <=> r2_hidden(sK6(u1_struct_0(sK0),sK1),sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.57/0.57  fof(f151,plain,(
% 1.57/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_8),
% 1.57/0.57    inference(avatar_component_clause,[],[f149])).
% 1.57/0.57  fof(f149,plain,(
% 1.57/0.57    spl8_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.57/0.57  fof(f242,plain,(
% 1.57/0.57    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl8_16),
% 1.57/0.57    inference(avatar_component_clause,[],[f240])).
% 1.57/0.57  fof(f240,plain,(
% 1.57/0.57    spl8_16 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.57/0.57  fof(f159,plain,(
% 1.57/0.57    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl8_10),
% 1.57/0.57    inference(avatar_component_clause,[],[f158])).
% 1.57/0.57  fof(f158,plain,(
% 1.57/0.57    spl8_10 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.57/0.57  fof(f141,plain,(
% 1.57/0.57    v13_waybel_0(sK1,sK0) | ~spl8_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f139])).
% 1.57/0.57  fof(f139,plain,(
% 1.57/0.57    spl8_6 <=> v13_waybel_0(sK1,sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.57/0.57  fof(f131,plain,(
% 1.57/0.57    l1_orders_2(sK0) | ~spl8_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f129])).
% 1.57/0.57  fof(f129,plain,(
% 1.57/0.57    spl8_4 <=> l1_orders_2(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.57/0.57  fof(f499,plain,(
% 1.57/0.57    r1_orders_2(sK0,k3_yellow_0(sK0),sK6(u1_struct_0(sK0),sK1)) | (~spl8_4 | ~spl8_7 | ~spl8_12 | ~spl8_17 | ~spl8_30)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f469,f293])).
% 1.57/0.57  fof(f293,plain,(
% 1.57/0.57    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_4 | ~spl8_7 | ~spl8_12 | ~spl8_17)),
% 1.57/0.57    inference(subsumption_resolution,[],[f261,f292])).
% 1.57/0.57  fof(f292,plain,(
% 1.57/0.57    ( ! [X5] : (r2_lattice3(sK0,k1_xboole_0,X5) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | (~spl8_4 | ~spl8_7)),
% 1.57/0.57    inference(forward_demodulation,[],[f289,f264])).
% 1.57/0.57  fof(f264,plain,(
% 1.57/0.57    k1_xboole_0 = k2_subset_1(k1_xboole_0) | ~spl8_7),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f79,f170,f105])).
% 1.57/0.57  fof(f105,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f68])).
% 1.57/0.57  fof(f68,plain,(
% 1.57/0.57    ! [X0,X1] : ((r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f41,f67])).
% 1.57/0.57  fof(f67,plain,(
% 1.57/0.57    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK7(X0,X1),X1) & m1_subset_1(sK7(X0,X1),X0)))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(flattening,[],[f40])).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).
% 1.57/0.57  fof(f170,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(X0,k2_subset_1(k1_xboole_0))) ) | ~spl8_7),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f146,f79,f107])).
% 1.57/0.57  fof(f107,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f44])).
% 1.57/0.57  fof(f44,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.57/0.57  fof(f146,plain,(
% 1.57/0.57    v1_xboole_0(k1_xboole_0) | ~spl8_7),
% 1.57/0.57    inference(avatar_component_clause,[],[f144])).
% 1.57/0.57  fof(f144,plain,(
% 1.57/0.57    spl8_7 <=> v1_xboole_0(k1_xboole_0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.57/0.57  fof(f79,plain,(
% 1.57/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.57/0.57  fof(f289,plain,(
% 1.57/0.57    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_lattice3(sK0,k2_subset_1(k1_xboole_0),X5)) ) | (~spl8_4 | ~spl8_7)),
% 1.57/0.57    inference(resolution,[],[f196,f170])).
% 1.57/0.57  fof(f196,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_lattice3(sK0,X0,X1)) ) | ~spl8_4),
% 1.57/0.57    inference(resolution,[],[f94,f131])).
% 1.57/0.57  fof(f94,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f63])).
% 1.57/0.57  fof(f63,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f61,f62])).
% 1.57/0.57  fof(f62,plain,(
% 1.57/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f61,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(rectify,[],[f60])).
% 1.57/0.57  fof(f60,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(nnf_transformation,[],[f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(flattening,[],[f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 1.57/0.57  fof(f261,plain,(
% 1.57/0.57    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl8_4 | ~spl8_12 | ~spl8_17)),
% 1.57/0.57    inference(subsumption_resolution,[],[f260,f131])).
% 1.57/0.57  fof(f260,plain,(
% 1.57/0.57    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | (~spl8_12 | ~spl8_17)),
% 1.57/0.57    inference(subsumption_resolution,[],[f257,f192])).
% 1.57/0.57  fof(f192,plain,(
% 1.57/0.57    r1_yellow_0(sK0,k1_xboole_0) | ~spl8_12),
% 1.57/0.57    inference(avatar_component_clause,[],[f190])).
% 1.57/0.57  fof(f190,plain,(
% 1.57/0.57    spl8_12 <=> r1_yellow_0(sK0,k1_xboole_0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.57/0.57  fof(f257,plain,(
% 1.57/0.57    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~r2_lattice3(sK0,k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~l1_orders_2(sK0)) ) | ~spl8_17),
% 1.57/0.57    inference(superposition,[],[f112,f248])).
% 1.57/0.57  fof(f248,plain,(
% 1.57/0.57    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_17),
% 1.57/0.57    inference(avatar_component_clause,[],[f246])).
% 1.57/0.57  fof(f246,plain,(
% 1.57/0.57    spl8_17 <=> k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.57/0.57  fof(f112,plain,(
% 1.57/0.57    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 1.57/0.57    inference(subsumption_resolution,[],[f108,f97])).
% 1.57/0.57  fof(f97,plain,(
% 1.57/0.57    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f12])).
% 1.57/0.57  fof(f12,axiom,(
% 1.57/0.57    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.57/0.57  fof(f108,plain,(
% 1.57/0.57    ( ! [X4,X0,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.57/0.57    inference(equality_resolution,[],[f88])).
% 1.57/0.57  fof(f88,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | k1_yellow_0(X0,X1) != X2 | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f59])).
% 1.57/0.57  fof(f59,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f57,f58])).
% 1.57/0.57  fof(f58,plain,(
% 1.57/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_lattice3(X0,X1,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f57,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_lattice3(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(rectify,[],[f56])).
% 1.57/0.57  fof(f56,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(flattening,[],[f55])).
% 1.57/0.57  fof(f55,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 | (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2)) | k1_yellow_0(X0,X1) != X2)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(nnf_transformation,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(flattening,[],[f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,axiom,(
% 1.57/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.57/0.57  fof(f470,plain,(
% 1.57/0.57    spl8_30 | ~spl8_8 | spl8_13),
% 1.57/0.57    inference(avatar_split_clause,[],[f370,f210,f149,f467])).
% 1.57/0.57  fof(f210,plain,(
% 1.57/0.57    spl8_13 <=> u1_struct_0(sK0) = sK1),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.57/0.57  fof(f370,plain,(
% 1.57/0.57    m1_subset_1(sK6(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl8_8 | spl8_13)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f151,f211,f100])).
% 1.57/0.57  fof(f100,plain,(
% 1.57/0.57    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f65])).
% 1.57/0.57  fof(f65,plain,(
% 1.57/0.57    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f64])).
% 1.57/0.57  fof(f64,plain,(
% 1.57/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),X0)))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(flattening,[],[f37])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 1.57/0.57  fof(f211,plain,(
% 1.57/0.57    u1_struct_0(sK0) != sK1 | spl8_13),
% 1.57/0.57    inference(avatar_component_clause,[],[f210])).
% 1.57/0.57  fof(f442,plain,(
% 1.57/0.57    ~spl8_28 | ~spl8_8 | spl8_13),
% 1.57/0.57    inference(avatar_split_clause,[],[f369,f210,f149,f439])).
% 1.57/0.57  fof(f369,plain,(
% 1.57/0.57    ~r2_hidden(sK6(u1_struct_0(sK0),sK1),sK1) | (~spl8_8 | spl8_13)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f151,f211,f101])).
% 1.57/0.57  fof(f101,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f65])).
% 1.57/0.57  fof(f403,plain,(
% 1.57/0.57    spl8_16 | ~spl8_4 | ~spl8_17),
% 1.57/0.57    inference(avatar_split_clause,[],[f335,f246,f129,f240])).
% 1.57/0.57  fof(f335,plain,(
% 1.57/0.57    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | (~spl8_4 | ~spl8_17)),
% 1.57/0.57    inference(subsumption_resolution,[],[f259,f131])).
% 1.57/0.57  fof(f259,plain,(
% 1.57/0.57    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~spl8_17),
% 1.57/0.57    inference(superposition,[],[f97,f248])).
% 1.57/0.57  fof(f379,plain,(
% 1.57/0.57    spl8_10 | spl8_5 | ~spl8_11),
% 1.57/0.57    inference(avatar_split_clause,[],[f353,f176,f134,f158])).
% 1.57/0.57  fof(f134,plain,(
% 1.57/0.57    spl8_5 <=> v1_xboole_0(sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.57/0.57  fof(f176,plain,(
% 1.57/0.57    spl8_11 <=> m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.57/0.57  fof(f353,plain,(
% 1.57/0.57    r2_hidden(k3_yellow_0(sK0),sK1) | (spl8_5 | ~spl8_11)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f136,f177,f99])).
% 1.57/0.57  fof(f99,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f36])).
% 1.57/0.57  fof(f36,plain,(
% 1.57/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.57/0.57    inference(flattening,[],[f35])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.57/0.57  fof(f177,plain,(
% 1.57/0.57    m1_subset_1(k3_yellow_0(sK0),sK1) | ~spl8_11),
% 1.57/0.57    inference(avatar_component_clause,[],[f176])).
% 1.57/0.57  fof(f136,plain,(
% 1.57/0.57    ~v1_xboole_0(sK1) | spl8_5),
% 1.57/0.57    inference(avatar_component_clause,[],[f134])).
% 1.57/0.57  fof(f363,plain,(
% 1.57/0.57    ~spl8_8 | ~spl8_13 | ~spl8_22),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f362])).
% 1.57/0.57  fof(f362,plain,(
% 1.57/0.57    $false | (~spl8_8 | ~spl8_13 | ~spl8_22)),
% 1.57/0.57    inference(subsumption_resolution,[],[f356,f351])).
% 1.57/0.57  fof(f351,plain,(
% 1.57/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl8_22),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f349,f110])).
% 1.57/0.57  fof(f110,plain,(
% 1.57/0.57    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.57/0.57    inference(equality_resolution,[],[f102])).
% 1.57/0.57  fof(f102,plain,(
% 1.57/0.57    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f66])).
% 1.57/0.57  fof(f66,plain,(
% 1.57/0.57    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(nnf_transformation,[],[f39])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f15])).
% 1.57/0.57  fof(f15,axiom,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 1.57/0.57  fof(f349,plain,(
% 1.57/0.57    v1_subset_1(sK1,sK1) | ~spl8_22),
% 1.57/0.57    inference(avatar_component_clause,[],[f347])).
% 1.57/0.57  fof(f347,plain,(
% 1.57/0.57    spl8_22 <=> v1_subset_1(sK1,sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.57/0.57  fof(f356,plain,(
% 1.57/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl8_8 | ~spl8_13)),
% 1.57/0.57    inference(superposition,[],[f151,f212])).
% 1.57/0.57  fof(f212,plain,(
% 1.57/0.57    u1_struct_0(sK0) = sK1 | ~spl8_13),
% 1.57/0.57    inference(avatar_component_clause,[],[f210])).
% 1.57/0.57  fof(f350,plain,(
% 1.57/0.57    spl8_22 | ~spl8_9 | ~spl8_13),
% 1.57/0.57    inference(avatar_split_clause,[],[f344,f210,f154,f347])).
% 1.57/0.57  fof(f154,plain,(
% 1.57/0.57    spl8_9 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.57/0.57  fof(f344,plain,(
% 1.57/0.57    v1_subset_1(sK1,sK1) | (~spl8_9 | ~spl8_13)),
% 1.57/0.57    inference(forward_demodulation,[],[f156,f212])).
% 1.57/0.57  fof(f156,plain,(
% 1.57/0.57    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_9),
% 1.57/0.57    inference(avatar_component_clause,[],[f154])).
% 1.57/0.57  fof(f341,plain,(
% 1.57/0.57    u1_struct_0(sK0) != sK1 | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.57/0.57    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.57  fof(f270,plain,(
% 1.57/0.57    spl8_9 | spl8_13 | ~spl8_8),
% 1.57/0.57    inference(avatar_split_clause,[],[f173,f149,f210,f154])).
% 1.57/0.57  fof(f173,plain,(
% 1.57/0.57    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_8),
% 1.57/0.57    inference(resolution,[],[f103,f151])).
% 1.57/0.57  fof(f103,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f66])).
% 1.57/0.57  fof(f249,plain,(
% 1.57/0.57    spl8_17 | ~spl8_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f164,f129,f246])).
% 1.57/0.57  fof(f164,plain,(
% 1.57/0.57    k3_yellow_0(sK0) = k1_yellow_0(sK0,k1_xboole_0) | ~spl8_4),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f131,f80])).
% 1.57/0.57  fof(f80,plain,(
% 1.57/0.57    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.57/0.57    inference(ennf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,axiom,(
% 1.57/0.57    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.57/0.57  fof(f193,plain,(
% 1.57/0.57    spl8_12 | spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f181,f129,f124,f119,f114,f190])).
% 1.57/0.57  fof(f114,plain,(
% 1.57/0.57    spl8_1 <=> v2_struct_0(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.57/0.57  fof(f119,plain,(
% 1.57/0.57    spl8_2 <=> v5_orders_2(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.57/0.57  fof(f124,plain,(
% 1.57/0.57    spl8_3 <=> v1_yellow_0(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.57/0.57  fof(f181,plain,(
% 1.57/0.57    r1_yellow_0(sK0,k1_xboole_0) | (spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f96])).
% 1.57/0.57  fof(f96,plain,(
% 1.57/0.57    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f32])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.57/0.57    inference(flattening,[],[f31])).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f21])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => r1_yellow_0(X0,k1_xboole_0))),
% 1.57/0.57    inference(pure_predicate_removal,[],[f13])).
% 1.57/0.57  fof(f13,axiom,(
% 1.57/0.57    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.57/0.57  fof(f126,plain,(
% 1.57/0.57    v1_yellow_0(sK0) | ~spl8_3),
% 1.57/0.57    inference(avatar_component_clause,[],[f124])).
% 1.57/0.57  fof(f121,plain,(
% 1.57/0.57    v5_orders_2(sK0) | ~spl8_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f119])).
% 1.57/0.57  fof(f116,plain,(
% 1.57/0.57    ~v2_struct_0(sK0) | spl8_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f114])).
% 1.57/0.57  fof(f163,plain,(
% 1.57/0.57    ~spl8_9 | spl8_10),
% 1.57/0.57    inference(avatar_split_clause,[],[f162,f158,f154])).
% 1.57/0.57  fof(f162,plain,(
% 1.57/0.57    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl8_10),
% 1.57/0.57    inference(subsumption_resolution,[],[f77,f160])).
% 1.57/0.57  fof(f160,plain,(
% 1.57/0.57    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl8_10),
% 1.57/0.57    inference(avatar_component_clause,[],[f158])).
% 1.57/0.57  fof(f77,plain,(
% 1.57/0.57    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  fof(f49,plain,(
% 1.57/0.57    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f46,f48,f47])).
% 1.57/0.57  fof(f47,plain,(
% 1.57/0.57    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f46,plain,(
% 1.57/0.57    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.57/0.57    inference(flattening,[],[f45])).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.57/0.57    inference(nnf_transformation,[],[f23])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.57/0.57    inference(flattening,[],[f22])).
% 1.57/0.57  fof(f22,plain,(
% 1.57/0.57    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f20])).
% 1.57/0.57  fof(f20,plain,(
% 1.57/0.57    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.57/0.57    inference(pure_predicate_removal,[],[f19])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.57/0.57    inference(pure_predicate_removal,[],[f18])).
% 1.57/0.57  fof(f18,plain,(
% 1.57/0.57    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.57/0.57    inference(pure_predicate_removal,[],[f17])).
% 1.57/0.57  fof(f17,negated_conjecture,(
% 1.57/0.57    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.57/0.57    inference(negated_conjecture,[],[f16])).
% 1.57/0.57  fof(f16,conjecture,(
% 1.57/0.57    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.57/0.57  fof(f161,plain,(
% 1.57/0.57    spl8_9 | ~spl8_10),
% 1.57/0.57    inference(avatar_split_clause,[],[f76,f158,f154])).
% 1.57/0.57  fof(f76,plain,(
% 1.57/0.57    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  fof(f152,plain,(
% 1.57/0.57    spl8_8),
% 1.57/0.57    inference(avatar_split_clause,[],[f75,f149])).
% 1.57/0.57  fof(f75,plain,(
% 1.57/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  fof(f147,plain,(
% 1.57/0.57    spl8_7),
% 1.57/0.57    inference(avatar_split_clause,[],[f78,f144])).
% 1.57/0.57  fof(f78,plain,(
% 1.57/0.57    v1_xboole_0(k1_xboole_0)),
% 1.57/0.57    inference(cnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    v1_xboole_0(k1_xboole_0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.57/0.57  fof(f142,plain,(
% 1.57/0.57    spl8_6),
% 1.57/0.57    inference(avatar_split_clause,[],[f74,f139])).
% 1.57/0.57  fof(f74,plain,(
% 1.57/0.57    v13_waybel_0(sK1,sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  fof(f137,plain,(
% 1.57/0.57    ~spl8_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f73,f134])).
% 1.57/0.57  fof(f73,plain,(
% 1.57/0.57    ~v1_xboole_0(sK1)),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  fof(f132,plain,(
% 1.57/0.57    spl8_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f72,f129])).
% 1.57/0.57  fof(f72,plain,(
% 1.57/0.57    l1_orders_2(sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  fof(f127,plain,(
% 1.57/0.57    spl8_3),
% 1.57/0.57    inference(avatar_split_clause,[],[f71,f124])).
% 1.57/0.57  fof(f71,plain,(
% 1.57/0.57    v1_yellow_0(sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  fof(f122,plain,(
% 1.57/0.57    spl8_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f70,f119])).
% 1.57/0.57  fof(f70,plain,(
% 1.57/0.57    v5_orders_2(sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  fof(f117,plain,(
% 1.57/0.57    ~spl8_1),
% 1.57/0.57    inference(avatar_split_clause,[],[f69,f114])).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    ~v2_struct_0(sK0)),
% 1.57/0.57    inference(cnf_transformation,[],[f49])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (32445)------------------------------
% 1.57/0.57  % (32445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (32445)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (32445)Memory used [KB]: 11129
% 1.57/0.57  % (32445)Time elapsed: 0.159 s
% 1.57/0.57  % (32445)------------------------------
% 1.57/0.57  % (32445)------------------------------
% 1.57/0.57  % (32421)Success in time 0.211 s
%------------------------------------------------------------------------------
