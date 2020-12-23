%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1651+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:15 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   94 (1127 expanded)
%              Number of leaves         :   17 ( 382 expanded)
%              Depth                    :   13
%              Number of atoms          :  555 (9824 expanded)
%              Number of equality atoms :   14 (  55 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f535,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f85,f141,f534])).

fof(f534,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f45,f46,f48,f142,f144,f208,f176,f177,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f177,plain,
    ( r1_orders_2(sK0,sK6(sK0,k3_waybel_0(sK0,sK1),sK2),sK5(sK0,sK1,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f47,f95,f142,f143,f72])).

fof(f72,plain,(
    ! [X6,X0,X1] :
      ( r1_orders_2(X0,X6,sK5(X0,X1,X6))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,X6,sK5(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ( ( ! [X4] :
                          ( ~ r2_hidden(X4,X1)
                          | ~ r1_orders_2(X0,sK3(X0,X1,X2),X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                    & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                        & r1_orders_2(X0,sK3(X0,X1,X2),sK4(X0,X1,X2))
                        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                      | r2_hidden(sK3(X0,X1,X2),X2) )
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X6,X7)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                            & r1_orders_2(X0,X6,sK5(X0,X1,X6))
                            & m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f36,f35,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r1_orders_2(X0,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r1_orders_2(X0,X3,X5)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r1_orders_2(X0,sK3(X0,X1,X2),X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r1_orders_2(X0,sK3(X0,X1,X2),X5)
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r1_orders_2(X0,sK3(X0,X1,X2),X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r1_orders_2(X0,sK3(X0,X1,X2),sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r1_orders_2(X0,X6,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r1_orders_2(X0,X6,sK5(X0,X1,X6))
        & m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r1_orders_2(X0,X3,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X6,X7)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ? [X8] :
                              ( r2_hidden(X8,X1)
                              & r1_orders_2(X0,X6,X8)
                              & m1_subset_1(X8,u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X3,X4)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X3,X4)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k3_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X3,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X3,X4)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X3,X4)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X3,X4)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k3_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_waybel_0)).

fof(f143,plain,
    ( r2_hidden(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),k3_waybel_0(sK0,sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f48,f83,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f83,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl8_2
  <=> r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f95,plain,(
    m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f46,f47,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_0)).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
      | ~ r2_lattice3(sK0,sK1,sK2) )
    & ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
      | r2_lattice3(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                  | ~ r2_lattice3(X0,X1,X2) )
                & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                  | r2_lattice3(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,X1),X2)
                | ~ r2_lattice3(sK0,X1,X2) )
              & ( r2_lattice3(sK0,k3_waybel_0(sK0,X1),X2)
                | r2_lattice3(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,X1),X2)
              | ~ r2_lattice3(sK0,X1,X2) )
            & ( r2_lattice3(sK0,k3_waybel_0(sK0,X1),X2)
              | r2_lattice3(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X2)
            | ~ r2_lattice3(sK0,sK1,X2) )
          & ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X2)
            | r2_lattice3(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X2)
          | ~ r2_lattice3(sK0,sK1,X2) )
        & ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),X2)
          | r2_lattice3(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
        | ~ r2_lattice3(sK0,sK1,sK2) )
      & ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
        | r2_lattice3(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | ~ r2_lattice3(X0,X1,X2) )
              & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | r2_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | ~ r2_lattice3(X0,X1,X2) )
              & ( r2_lattice3(X0,k3_waybel_0(X0,X1),X2)
                | r2_lattice3(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <~> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_lattice3(X0,X1,X2)
              <~> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X2)
                <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_lattice3(X0,X1,X2)
              <=> r2_lattice3(X0,k3_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_0)).

fof(f176,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),u1_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f47,f95,f142,f143,f73])).

fof(f73,plain,(
    ! [X6,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f208,plain,
    ( r1_orders_2(sK0,sK5(sK0,sK1,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),sK2)
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f48,f78,f178,f176,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f178,plain,
    ( r2_hidden(sK5(sK0,sK1,sK6(sK0,k3_waybel_0(sK0,sK1),sK2)),sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f47,f95,f142,f143,f71])).

fof(f71,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,
    ( r2_lattice3(sK0,sK1,sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_1
  <=> r2_lattice3(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f144,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,k3_waybel_0(sK0,sK1),sK2),sK2)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f48,f83,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f142,plain,
    ( m1_subset_1(sK6(sK0,k3_waybel_0(sK0,sK1),sK2),u1_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f48,f83,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f141,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f43,f44,f46,f88,f88,f103,f115,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f115,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f89,f88,f47,f95,f88,f106,f70])).

fof(f70,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k3_waybel_0(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k3_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f106,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),k3_waybel_0(sK0,sK1))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f82,f48,f88,f90,f60])).

fof(f90,plain,
    ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK2),sK2)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f46,f48,f79,f63])).

fof(f79,plain,
    ( ~ r2_lattice3(sK0,sK1,sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f82,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f89,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f46,f48,f79,f62])).

fof(f103,plain,
    ( r3_orders_2(sK0,sK6(sK0,sK1,sK2),sK6(sK0,sK1,sK2))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f86,f43,f44,f46,f88,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ sP7(X0) ) ),
    inference(general_splitting,[],[f66,f74_D])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP7(X0) ) ),
    inference(cnf_transformation,[],[f74_D])).

fof(f74_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP7(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f86,plain,(
    sP7(sK0) ),
    inference(unit_resulting_resolution,[],[f48,f74])).

fof(f88,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f46,f48,f79,f61])).

fof(f44,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f49,f81,f77])).

fof(f49,plain,
    ( r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f50,f81,f77])).

fof(f50,plain,
    ( ~ r2_lattice3(sK0,k3_waybel_0(sK0,sK1),sK2)
    | ~ r2_lattice3(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
