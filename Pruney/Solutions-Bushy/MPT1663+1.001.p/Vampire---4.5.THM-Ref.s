%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1663+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  177 (2609 expanded)
%              Number of leaves         :   34 ( 835 expanded)
%              Depth                    :   20
%              Number of atoms          : 1006 (36449 expanded)
%              Number of equality atoms :   40 (3802 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f438,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f186,f191,f196,f201,f205,f292,f437])).

fof(f437,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f409,f402])).

fof(f402,plain,
    ( ~ r1_lattice3(sK0,sK2,sK7(sK0,sK1,sK2))
    | ~ spl10_1
    | spl10_2
    | spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f82,f84,f339,f222,f387,f390,f137])).

fof(f137,plain,(
    ! [X4,X2,X0] :
      ( ~ v5_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X4,k2_yellow_0(X0,X2)) ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X1)
      | ~ r1_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK8(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK8(X0,X1,X2))
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f39,f76])).

fof(f76,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK8(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f390,plain,
    ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK2),k2_yellow_0(sK0,sK2))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f84,f185,f222,f86,f87,f384,f387,f96])).

fof(f96,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK4(X0,X1),X1)
                & r1_orders_2(X0,sK3(X0,X1),sK4(X0,X1))
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f62,f64,f63])).

fof(f63,plain,(
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
            & r1_orders_2(X0,sK3(X0,X1),X3)
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK3(X0,X1),X3)
          & r2_hidden(sK3(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r1_orders_2(X0,sK3(X0,X1),sK4(X0,X1))
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f384,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),sK1)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f208,f81,f84,f200,f85,f195,f180,f87,f110])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_finset_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | r2_hidden(sK7(X0,X1,X4),X1)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ( ! [X3] :
                    ( ~ r1_lattice3(X0,sK6(X0,X1),X3)
                    | ~ r2_hidden(X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(X1))
                & v1_finset_1(sK6(X0,X1)) ) )
            & ( ! [X4] :
                  ( ( r1_lattice3(X0,X4,sK7(X0,X1,X4))
                    & r2_hidden(sK7(X0,X1,X4),X1)
                    & m1_subset_1(sK7(X0,X1,X4),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              | ~ v2_waybel_0(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f72,f74,f73])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_lattice3(X0,X2,X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ! [X3] :
            ( ~ r1_lattice3(X0,sK6(X0,X1),X3)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r1_lattice3(X0,X4,X5)
          & r2_hidden(X5,X1)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,X4,sK7(X0,X1,X4))
        & r2_hidden(sK7(X0,X1,X4),X1)
        & m1_subset_1(sK7(X0,X1,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_lattice3(X0,X2,X3)
                      | ~ r2_hidden(X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r1_lattice3(X0,X4,X5)
                      & r2_hidden(X5,X1)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              | ~ v2_waybel_0(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_lattice3(X0,X2,X3)
                      | ~ r2_hidden(X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_lattice3(X0,X2,X3)
                      & r2_hidden(X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X2) )
              | ~ v2_waybel_0(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_lattice3(X0,X2,X3)
                      | ~ r2_hidden(X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r1_lattice3(X0,X2,X3)
                      & r2_hidden(X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X2) )
              | ~ v2_waybel_0(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ? [X3] :
                    ( r1_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_waybel_0)).

fof(f180,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl10_1
  <=> v2_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f195,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl10_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f85,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ( ( ~ r2_hidden(k2_yellow_0(sK0,sK2),sK1)
        & k1_xboole_0 != sK2
        & m1_subset_1(sK2,k1_zfmisc_1(sK1))
        & v1_finset_1(sK2) )
      | ~ v2_waybel_0(sK1,sK0) )
    & ( ! [X3] :
          ( r2_hidden(k2_yellow_0(sK0,X3),sK1)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
          | ~ v1_finset_1(X3) )
      | v2_waybel_0(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f56,f59,f58,f57])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
              | ~ v2_waybel_0(X1,X0) )
            & ( ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X1)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              | v2_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(sK0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,sK0) )
          & ( ! [X3] :
                ( r2_hidden(k2_yellow_0(sK0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v2_waybel_0(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ~ r2_hidden(k2_yellow_0(sK0,X2),X1)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(X1))
              & v1_finset_1(X2) )
          | ~ v2_waybel_0(X1,sK0) )
        & ( ! [X3] :
              ( r2_hidden(k2_yellow_0(sK0,X3),X1)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X3) )
          | v2_waybel_0(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( ? [X2] :
            ( ~ r2_hidden(k2_yellow_0(sK0,X2),sK1)
            & k1_xboole_0 != X2
            & m1_subset_1(X2,k1_zfmisc_1(sK1))
            & v1_finset_1(X2) )
        | ~ v2_waybel_0(sK1,sK0) )
      & ( ! [X3] :
            ( r2_hidden(k2_yellow_0(sK0,X3),sK1)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
            | ~ v1_finset_1(X3) )
        | v2_waybel_0(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k2_yellow_0(sK0,X2),sK1)
        & k1_xboole_0 != X2
        & m1_subset_1(X2,k1_zfmisc_1(sK1))
        & v1_finset_1(X2) )
   => ( ~ r2_hidden(k2_yellow_0(sK0,sK2),sK1)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK2,k1_zfmisc_1(sK1))
      & v1_finset_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k2_yellow_0(X0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k2_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v2_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v2_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                    & v1_finset_1(X2) )
                 => ( k1_xboole_0 != X2
                   => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k2_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_waybel_0)).

fof(f200,plain,
    ( v1_finset_1(sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl10_5
  <=> v1_finset_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f81,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f208,plain,(
    ~ v2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f84,f83,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f83,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f87,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f86,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f185,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,sK2),sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl10_2
  <=> r2_hidden(k2_yellow_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f387,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f87,f384,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f222,plain,(
    ! [X0] : m1_subset_1(k2_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f84,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f339,plain,
    ( r2_yellow_0(sK0,sK2)
    | spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f80,f81,f82,f84,f83,f295,f200,f312,f206])).

fof(f206,plain,(
    ! [X2,X0] :
      ( ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_yellow_0(X0,X2)
      | v1_xboole_0(X2)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f104,f94])).

fof(f104,plain,(
    ! [X2,X0] :
      ( r2_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | v1_xboole_0(X2)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ( ~ r2_yellow_0(X0,sK5(X0))
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(sK5(X0))
            & ~ v1_xboole_0(sK5(X0)) ) )
        & ( ! [X2] :
              ( r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f67,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_finset_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( ~ r2_yellow_0(X0,sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_finset_1(sK5(X0))
        & ~ v1_xboole_0(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ~ r2_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X2] :
              ( r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( ( v2_lattice3(X0)
          | ? [X1] :
              ( ~ r2_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X1] :
              ( r2_yellow_0(X0,X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X1)
              | v1_xboole_0(X1) )
          | ~ v2_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_lattice3(X0)
      <=> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_lattice3(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) )
           => r2_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_yellow_0)).

fof(f312,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f309,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f309,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f211,f304,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f304,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f195,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f211,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f87,f132])).

fof(f295,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_3 ),
    inference(unit_resulting_resolution,[],[f190,f142])).

fof(f142,plain,(
    ! [X0] :
      ( sQ9_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f102,f139])).

fof(f139,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f102,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f190,plain,
    ( ~ sQ9_eqProxy(k1_xboole_0,sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl10_3
  <=> sQ9_eqProxy(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f80,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f84,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f82,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f409,plain,
    ( r1_lattice3(sK0,sK2,sK7(sK0,sK1,sK2))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f208,f81,f84,f200,f85,f195,f180,f87,f111])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_finset_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | r1_lattice3(X0,X4,sK7(X0,X1,X4))
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f292,plain,
    ( spl10_1
    | ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl10_1
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f287,f285])).

fof(f285,plain,
    ( r1_lattice3(sK0,sK6(sK0,sK1),k2_yellow_0(sK0,sK6(sK0,sK1)))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f82,f84,f222,f281,f138])).

fof(f138,plain,(
    ! [X2,X0] :
      ( ~ r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f281,plain,
    ( r2_yellow_0(sK0,sK6(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f80,f81,f82,f84,f83,f242,f253,f276,f206])).

fof(f276,plain,
    ( ~ v1_xboole_0(sK6(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f273,f142])).

fof(f273,plain,
    ( ~ sQ9_eqProxy(k1_xboole_0,sK6(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f175,f266,f175,f267,f172])).

fof(f172,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_lattice3(X0,X2,X4)
      | ~ sQ9_eqProxy(X2,X3)
      | ~ sQ9_eqProxy(X4,X5)
      | ~ sQ9_eqProxy(X0,X1)
      | r1_lattice3(X1,X3,X5) ) ),
    inference(equality_proxy_axiom,[],[f139])).

fof(f267,plain,
    ( ~ r1_lattice3(sK0,sK6(sK0,sK1),o_2_8_waybel_0(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f208,f81,f84,f181,f87,f262,f259,f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_lattice3(X0,sK6(X0,X1),X3)
      | v2_waybel_0(X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f259,plain,(
    m1_subset_1(o_2_8_waybel_0(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f85,f210,f87,f256,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
         => m1_subset_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_subset_1)).

fof(f256,plain,(
    m2_subset_1(o_2_8_waybel_0(sK0,sK1),u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f80,f81,f82,f83,f84,f85,f86,f87,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v13_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => m2_subset_1(o_2_8_waybel_0(X0,X1),u1_struct_0(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_8_waybel_0)).

fof(f210,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f208,f207,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f207,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f84,f93])).

fof(f93,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f262,plain,(
    r2_hidden(o_2_8_waybel_0(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f85,f258,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f258,plain,(
    m1_subset_1(o_2_8_waybel_0(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f85,f210,f87,f256,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_m2_subset_1)).

fof(f181,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f179])).

fof(f266,plain,(
    r1_lattice3(sK0,k1_xboole_0,o_2_8_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f84,f259,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f175,plain,(
    ! [X0] : sQ9_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f139])).

fof(f253,plain,
    ( m1_subset_1(sK6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f250,f133])).

fof(f250,plain,
    ( r1_tarski(sK6(sK0,sK1),u1_struct_0(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f211,f247,f135])).

fof(f247,plain,
    ( r1_tarski(sK6(sK0,sK1),sK1)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f246,f132])).

fof(f246,plain,
    ( m1_subset_1(sK6(sK0,sK1),k1_zfmisc_1(sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f208,f81,f84,f181,f87,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | m1_subset_1(sK6(X0,X1),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f242,plain,
    ( v1_finset_1(sK6(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f208,f81,f84,f181,f87,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | v1_finset_1(sK6(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f287,plain,
    ( ~ r1_lattice3(sK0,sK6(sK0,sK1),k2_yellow_0(sK0,sK6(sK0,sK1)))
    | spl10_1
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f208,f81,f84,f181,f87,f222,f275,f117])).

fof(f275,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK6(sK0,sK1)),sK1)
    | spl10_1
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f242,f246,f273,f204])).

fof(f204,plain,
    ( ! [X3] :
        ( ~ v1_finset_1(X3)
        | r2_hidden(k2_yellow_0(sK0,X3),sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | sQ9_eqProxy(k1_xboole_0,X3) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl10_6
  <=> ! [X3] :
        ( r2_hidden(k2_yellow_0(sK0,X3),sK1)
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | sQ9_eqProxy(k1_xboole_0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f205,plain,
    ( spl10_1
    | spl10_6 ),
    inference(avatar_split_clause,[],[f141,f203,f179])).

fof(f141,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK0,X3),sK1)
      | sQ9_eqProxy(k1_xboole_0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | v2_waybel_0(sK1,sK0) ) ),
    inference(equality_proxy_replacement,[],[f88,f139])).

fof(f88,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK0,X3),sK1)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | v2_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f201,plain,
    ( ~ spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f89,f198,f179])).

fof(f89,plain,
    ( v1_finset_1(sK2)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

% (21164)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f196,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f90,f193,f179])).

fof(f90,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f191,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f140,f188,f179])).

fof(f140,plain,
    ( ~ sQ9_eqProxy(k1_xboole_0,sK2)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(equality_proxy_replacement,[],[f91,f139])).

fof(f91,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f186,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f92,f183,f179])).

fof(f92,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,sK2),sK1)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

%------------------------------------------------------------------------------
