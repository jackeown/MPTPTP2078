%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1662+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:17 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
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
fof(f429,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f183,f188,f193,f198,f202,f285,f428])).

fof(f428,plain,
    ( ~ spl10_1
    | spl10_2
    | spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f400,f393])).

fof(f393,plain,
    ( ~ r2_lattice3(sK0,sK2,sK7(sK0,sK1,sK2))
    | ~ spl10_1
    | spl10_2
    | spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f80,f82,f332,f219,f380,f382,f134])).

fof(f134,plain,(
    ! [X4,X2,X0] :
      ( ~ v5_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k1_yellow_0(X0,X2),X4) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X1,X4)
      | ~ r2_lattice3(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,X1,sK8(X0,X1,X2))
                  & r2_lattice3(X0,X2,sK8(X0,X1,X2))
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X1,sK8(X0,X1,X2))
        & r2_lattice3(X0,X2,sK8(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
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
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f382,plain,
    ( ~ r1_orders_2(sK0,k1_yellow_0(sK0,sK2),sK7(sK0,sK1,sK2))
    | ~ spl10_1
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f82,f182,f219,f84,f85,f377,f380,f94])).

fof(f94,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X5,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK4(X0,X1),X1)
                & r1_orders_2(X0,sK4(X0,X1),sK3(X0,X1))
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f60,f62,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X3,X2)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,X3,sK3(X0,X1))
            & r2_hidden(sK3(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X3,sK3(X0,X1))
          & r2_hidden(sK3(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r1_orders_2(X0,sK4(X0,X1),sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X5,X4)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X3,X2)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
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
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_waybel_0)).

fof(f377,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),sK1)
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f205,f79,f82,f197,f83,f192,f177,f85,f108])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_finset_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | r2_hidden(sK7(X0,X1,X4),X1)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ( ! [X3] :
                    ( ~ r2_lattice3(X0,sK6(X0,X1),X3)
                    | ~ r2_hidden(X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(X1))
                & v1_finset_1(sK6(X0,X1)) ) )
            & ( ! [X4] :
                  ( ( r2_lattice3(X0,X4,sK7(X0,X1,X4))
                    & r2_hidden(sK7(X0,X1,X4),X1)
                    & m1_subset_1(sK7(X0,X1,X4),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              | ~ v1_waybel_0(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f70,f72,f71])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_lattice3(X0,X2,X3)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X1))
          & v1_finset_1(X2) )
     => ( ! [X3] :
            ( ~ r2_lattice3(X0,sK6(X0,X1),X3)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(X1))
        & v1_finset_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( r2_lattice3(X0,X4,X5)
          & r2_hidden(X5,X1)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,X4,sK7(X0,X1,X4))
        & r2_hidden(sK7(X0,X1,X4),X1)
        & m1_subset_1(sK7(X0,X1,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r2_lattice3(X0,X2,X3)
                      | ~ r2_hidden(X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( r2_lattice3(X0,X4,X5)
                      & r2_hidden(X5,X1)
                      & m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X4) )
              | ~ v1_waybel_0(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r2_lattice3(X0,X2,X3)
                      | ~ r2_hidden(X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r2_lattice3(X0,X2,X3)
                      & r2_hidden(X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X2) )
              | ~ v1_waybel_0(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v1_waybel_0(X1,X0)
                & ~ v1_xboole_0(X1) )
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ r2_lattice3(X0,X2,X3)
                      | ~ r2_hidden(X3,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( r2_lattice3(X0,X2,X3)
                      & r2_hidden(X3,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X2) )
              | ~ v1_waybel_0(X1,X0)
              | v1_xboole_0(X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ? [X3] :
                    ( r2_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v1_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ? [X3] :
                    ( r2_lattice3(X0,X2,X3)
                    & r2_hidden(X3,X1)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_waybel_0)).

fof(f177,plain,
    ( v1_waybel_0(sK1,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl10_1
  <=> v1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f192,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl10_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f83,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ( ~ r2_hidden(k1_yellow_0(sK0,sK2),sK1)
        & k1_xboole_0 != sK2
        & m1_subset_1(sK2,k1_zfmisc_1(sK1))
        & v1_finset_1(sK2) )
      | ~ v1_waybel_0(sK1,sK0) )
    & ( ! [X3] :
          ( r2_hidden(k1_yellow_0(sK0,X3),sK1)
          | k1_xboole_0 = X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
          | ~ v1_finset_1(X3) )
      | v1_waybel_0(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v12_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f54,f57,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
              | ~ v1_waybel_0(X1,X0) )
            & ( ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X1)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              | v1_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k1_yellow_0(sK0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,sK0) )
          & ( ! [X3] :
                ( r2_hidden(k1_yellow_0(sK0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v1_waybel_0(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v12_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ~ r2_hidden(k1_yellow_0(sK0,X2),X1)
              & k1_xboole_0 != X2
              & m1_subset_1(X2,k1_zfmisc_1(X1))
              & v1_finset_1(X2) )
          | ~ v1_waybel_0(X1,sK0) )
        & ( ! [X3] :
              ( r2_hidden(k1_yellow_0(sK0,X3),X1)
              | k1_xboole_0 = X3
              | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
              | ~ v1_finset_1(X3) )
          | v1_waybel_0(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v12_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( ? [X2] :
            ( ~ r2_hidden(k1_yellow_0(sK0,X2),sK1)
            & k1_xboole_0 != X2
            & m1_subset_1(X2,k1_zfmisc_1(sK1))
            & v1_finset_1(X2) )
        | ~ v1_waybel_0(sK1,sK0) )
      & ( ! [X3] :
            ( r2_hidden(k1_yellow_0(sK0,X3),sK1)
            | k1_xboole_0 = X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
            | ~ v1_finset_1(X3) )
        | v1_waybel_0(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v12_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k1_yellow_0(sK0,X2),sK1)
        & k1_xboole_0 != X2
        & m1_subset_1(X2,k1_zfmisc_1(sK1))
        & v1_finset_1(X2) )
   => ( ~ r2_hidden(k1_yellow_0(sK0,sK2),sK1)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK2,k1_zfmisc_1(sK1))
      & v1_finset_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k1_yellow_0(X0,X3),X1)
                | k1_xboole_0 = X3
                | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X3) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k1_yellow_0(X0,X2),X1)
                & k1_xboole_0 != X2
                & m1_subset_1(X2,k1_zfmisc_1(X1))
                & v1_finset_1(X2) )
            | ~ v1_waybel_0(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) )
            | v1_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_waybel_0(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),X1)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
                | ~ v1_finset_1(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v12_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v12_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_waybel_0(X1,X0)
            <=> ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                    & v1_finset_1(X2) )
                 => ( k1_xboole_0 != X2
                   => r2_hidden(k1_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
                  & v1_finset_1(X2) )
               => ( k1_xboole_0 != X2
                 => r2_hidden(k1_yellow_0(X0,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_waybel_0)).

fof(f197,plain,
    ( v1_finset_1(sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl10_5
  <=> v1_finset_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f79,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f205,plain,(
    ~ v2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f82,f81,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f81,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f84,plain,(
    v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f182,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl10_2
  <=> r2_hidden(k1_yellow_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f380,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f85,f377,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f219,plain,(
    ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f82,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f332,plain,
    ( r1_yellow_0(sK0,sK2)
    | spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f82,f81,f288,f197,f305,f203])).

fof(f203,plain,(
    ! [X2,X0] :
      ( ~ v1_finset_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_yellow_0(X0,X2)
      | v1_xboole_0(X2)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f102,f92])).

fof(f102,plain,(
    ! [X2,X0] :
      ( r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_finset_1(X2)
      | v1_xboole_0(X2)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ( ~ r1_yellow_0(X0,sK5(X0))
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(sK5(X0))
            & ~ v1_xboole_0(sK5(X0)) ) )
        & ( ! [X2] :
              ( r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f65,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_yellow_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_finset_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( ~ r1_yellow_0(X0,sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & v1_finset_1(sK5(X0))
        & ~ v1_xboole_0(sK5(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ~ r1_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X2] :
              ( r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X2)
              | v1_xboole_0(X2) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v1_lattice3(X0)
          | ? [X1] :
              ( ~ r1_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X1] :
              ( r1_yellow_0(X0,X1)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v1_finset_1(X1)
              | v1_xboole_0(X1) )
          | ~ v1_lattice3(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v1_finset_1(X1)
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( r1_yellow_0(X0,X1)
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
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_finset_1(X1)
              & ~ v1_xboole_0(X1) )
           => r1_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_yellow_0)).

fof(f305,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f302,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
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

fof(f302,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f208,f297,f133])).

fof(f133,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f297,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f192,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f208,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f85,f130])).

fof(f288,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_3 ),
    inference(unit_resulting_resolution,[],[f187,f139])).

fof(f139,plain,(
    ! [X0] :
      ( sQ9_eqProxy(k1_xboole_0,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f100,f136])).

fof(f136,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f187,plain,
    ( ~ sQ9_eqProxy(k1_xboole_0,sK2)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl10_3
  <=> sQ9_eqProxy(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f78,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f82,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f80,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f400,plain,
    ( r2_lattice3(sK0,sK2,sK7(sK0,sK1,sK2))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f205,f79,f82,f197,f83,f192,f177,f85,f109])).

fof(f109,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_finset_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
      | r2_lattice3(X0,X4,sK7(X0,X1,X4))
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f285,plain,
    ( spl10_1
    | ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl10_1
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f281,f279])).

fof(f279,plain,
    ( r2_lattice3(sK0,sK6(sK0,sK1),k1_yellow_0(sK0,sK6(sK0,sK1)))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f80,f82,f219,f275,f135])).

fof(f135,plain,(
    ! [X2,X0] :
      ( ~ r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,X1)
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f275,plain,
    ( r1_yellow_0(sK0,sK6(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f82,f81,f238,f249,f270,f203])).

fof(f270,plain,
    ( ~ v1_xboole_0(sK6(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f267,f139])).

fof(f267,plain,
    ( ~ sQ9_eqProxy(k1_xboole_0,sK6(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f172,f261,f172,f262,f168])).

fof(f168,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_lattice3(X0,X2,X4)
      | ~ sQ9_eqProxy(X2,X3)
      | ~ sQ9_eqProxy(X4,X5)
      | ~ sQ9_eqProxy(X0,X1)
      | r2_lattice3(X1,X3,X5) ) ),
    inference(equality_proxy_axiom,[],[f136])).

fof(f262,plain,
    ( ~ r2_lattice3(sK0,sK6(sK0,sK1),o_2_7_waybel_0(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f205,f79,f82,f178,f85,f258,f255,f115])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_lattice3(X0,sK6(X0,X1),X3)
      | v1_waybel_0(X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f255,plain,(
    m1_subset_1(o_2_7_waybel_0(sK0,sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f83,f207,f85,f252,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,X0)
          | ~ m2_subset_1(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f252,plain,(
    m2_subset_1(o_2_7_waybel_0(sK0,sK1),u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f78,f79,f80,f81,f82,f83,f84,f85,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v12_waybel_0(X1,X0)
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => m2_subset_1(o_2_7_waybel_0(X0,X1),u1_struct_0(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_7_waybel_0)).

fof(f207,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f205,f204,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f204,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f82,f91])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f258,plain,(
    r2_hidden(o_2_7_waybel_0(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f83,f254,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f254,plain,(
    m1_subset_1(o_2_7_waybel_0(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f83,f207,f85,f252,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_subset_1(X2,X0,X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m2_subset_1(X2,X0,X1)
            | ~ m1_subset_1(X2,X1) )
          & ( m1_subset_1(X2,X1)
            | ~ m2_subset_1(X2,X0,X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m2_subset_1(X2,X0,X1)
        <=> m1_subset_1(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f178,plain,
    ( ~ v1_waybel_0(sK1,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f176])).

fof(f261,plain,(
    r2_lattice3(sK0,k1_xboole_0,o_2_7_waybel_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f82,f255,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f172,plain,(
    ! [X0] : sQ9_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f136])).

fof(f249,plain,
    ( m1_subset_1(sK6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f246,f131])).

fof(f246,plain,
    ( r1_tarski(sK6(sK0,sK1),u1_struct_0(sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f208,f243,f133])).

fof(f243,plain,
    ( r1_tarski(sK6(sK0,sK1),sK1)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f242,f130])).

fof(f242,plain,
    ( m1_subset_1(sK6(sK0,sK1),k1_zfmisc_1(sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f205,f79,f82,f178,f85,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | m1_subset_1(sK6(X0,X1),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f238,plain,
    ( v1_finset_1(sK6(sK0,sK1))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f205,f79,f82,f178,f85,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | v1_finset_1(sK6(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f281,plain,
    ( ~ r2_lattice3(sK0,sK6(sK0,sK1),k1_yellow_0(sK0,sK6(sK0,sK1)))
    | spl10_1
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f205,f79,f82,f178,f85,f219,f269,f115])).

fof(f269,plain,
    ( r2_hidden(k1_yellow_0(sK0,sK6(sK0,sK1)),sK1)
    | spl10_1
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f238,f242,f267,f201])).

fof(f201,plain,
    ( ! [X3] :
        ( ~ v1_finset_1(X3)
        | r2_hidden(k1_yellow_0(sK0,X3),sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | sQ9_eqProxy(k1_xboole_0,X3) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl10_6
  <=> ! [X3] :
        ( r2_hidden(k1_yellow_0(sK0,X3),sK1)
        | ~ v1_finset_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | sQ9_eqProxy(k1_xboole_0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f202,plain,
    ( spl10_1
    | spl10_6 ),
    inference(avatar_split_clause,[],[f138,f200,f176])).

fof(f138,plain,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK0,X3),sK1)
      | sQ9_eqProxy(k1_xboole_0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | v1_waybel_0(sK1,sK0) ) ),
    inference(equality_proxy_replacement,[],[f86,f136])).

fof(f86,plain,(
    ! [X3] :
      ( r2_hidden(k1_yellow_0(sK0,X3),sK1)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | v1_waybel_0(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f198,plain,
    ( ~ spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f87,f195,f176])).

fof(f87,plain,
    ( v1_finset_1(sK2)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f193,plain,
    ( ~ spl10_1
    | spl10_4 ),
    inference(avatar_split_clause,[],[f88,f190,f176])).

fof(f88,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f188,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f137,f185,f176])).

fof(f137,plain,
    ( ~ sQ9_eqProxy(k1_xboole_0,sK2)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(equality_proxy_replacement,[],[f89,f136])).

fof(f89,plain,
    ( k1_xboole_0 != sK2
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f183,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f90,f180,f176])).

fof(f90,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),sK1)
    | ~ v1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

%------------------------------------------------------------------------------
