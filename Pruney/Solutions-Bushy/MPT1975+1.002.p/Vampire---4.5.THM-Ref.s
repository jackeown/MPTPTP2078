%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1975+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:00 EST 2020

% Result     : Theorem 2.52s
% Output     : Refutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  148 (2977 expanded)
%              Number of leaves         :   28 ( 976 expanded)
%              Depth                    :   17
%              Number of atoms          :  966 (47324 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6915,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f135,f140,f144,f6222,f6849])).

fof(f6849,plain,
    ( ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f6848])).

fof(f6848,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f2386,f6847])).

fof(f6847,plain,
    ( ~ r2_hidden(k4_yellow_0(sK0),sK1)
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f6832,f6645])).

fof(f6645,plain,
    ( k4_yellow_0(sK0) = k13_lattice3(sK0,sK2,k7_waybel_1(sK0,sK2))
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f145,f70,f73,f139,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v11_waybel_1(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k4_yellow_0(X0) = k13_lattice3(X0,X1,k7_waybel_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_yellow_0(X0) = k13_lattice3(X0,X1,k7_waybel_1(X0,X1))
            & k3_yellow_0(X0) = k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_yellow_0(X0) = k13_lattice3(X0,X1,k7_waybel_1(X0,X1))
            & k3_yellow_0(X0) = k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v11_waybel_1(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k4_yellow_0(X0) = k13_lattice3(X0,X1,k7_waybel_1(X0,X1))
            & k3_yellow_0(X0) = k12_lattice3(X0,X1,k7_waybel_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow_5)).

fof(f139,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl9_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f73,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ( ~ r2_hidden(k7_waybel_1(sK0,sK2),sK1)
        & ~ r2_hidden(sK2,sK1)
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ v2_waybel_7(sK1,sK0) )
    & ( ! [X3] :
          ( r2_hidden(k7_waybel_1(sK0,X3),sK1)
          | r2_hidden(X3,sK1)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | v2_waybel_7(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & v2_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v1_lattice3(sK0)
    & v11_waybel_1(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                  & ~ r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) )
            & ( ! [X3] :
                  ( r2_hidden(k7_waybel_1(X0,X3),X1)
                  | r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | v2_waybel_7(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k7_waybel_1(sK0,X2),X1)
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v2_waybel_7(X1,sK0) )
          & ( ! [X3] :
                ( r2_hidden(k7_waybel_1(sK0,X3),X1)
                | r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            | v2_waybel_7(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & v2_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v1_lattice3(sK0)
      & v11_waybel_1(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( ~ r2_hidden(k7_waybel_1(sK0,X2),X1)
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ v2_waybel_7(X1,sK0) )
        & ( ! [X3] :
              ( r2_hidden(k7_waybel_1(sK0,X3),X1)
              | r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          | v2_waybel_7(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & v2_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( ? [X2] :
            ( ~ r2_hidden(k7_waybel_1(sK0,X2),sK1)
            & ~ r2_hidden(X2,sK1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ v2_waybel_7(sK1,sK0) )
      & ( ! [X3] :
            ( r2_hidden(k7_waybel_1(sK0,X3),sK1)
            | r2_hidden(X3,sK1)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        | v2_waybel_7(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & v2_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k7_waybel_1(sK0,X2),sK1)
        & ~ r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ~ r2_hidden(k7_waybel_1(sK0,sK2),sK1)
      & ~ r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_7(X1,X0) )
          & ( ! [X3] :
                ( r2_hidden(k7_waybel_1(X0,X3),X1)
                | r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | v2_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v2_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_hidden(k7_waybel_1(X0,X2),X1)
                & ~ r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v2_waybel_7(X1,X0) )
          & ( ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v2_waybel_7(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_7(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_7(X1,X0)
          <~> ! [X2] :
                ( r2_hidden(k7_waybel_1(X0,X2),X1)
                | r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v11_waybel_1(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v11_waybel_1(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v2_waybel_7(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(k7_waybel_1(X0,X2),X1)
                    | r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v11_waybel_1(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k7_waybel_1(X0,X2),X1)
                  | r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_waybel_7)).

fof(f70,plain,(
    v11_waybel_1(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f145,plain,(
    ~ v2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f73,f72,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f72,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f6832,plain,
    ( ~ r2_hidden(k13_lattice3(sK0,sK2,k7_waybel_1(sK0,sK2)),sK1)
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f67,f68,f69,f71,f73,f74,f75,f76,f124,f134,f139,f77,f129,f6667,f108])).

fof(f108,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v2_waybel_7(X1,X0)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r2_hidden(X5,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK6(X0,X1),X1)
                & ~ r2_hidden(sK5(X0,X1),X1)
                & r2_hidden(k13_lattice3(X0,sK5(X0,X1),sK6(X0,X1)),X1)
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f58,f60,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK5(X0,X1),X1)
            & r2_hidden(k13_lattice3(X0,sK5(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(k13_lattice3(X0,sK5(X0,X1),X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(k13_lattice3(X0,sK5(X0,X1),sK6(X0,X1)),X1)
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_waybel_7)).

fof(f6667,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f145,f73,f139,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_waybel_1(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_waybel_1)).

fof(f129,plain,
    ( ~ r2_hidden(k7_waybel_1(sK0,sK2),sK1)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl9_2
  <=> r2_hidden(k7_waybel_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f134,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f124,plain,
    ( v2_waybel_7(sK1,sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl9_1
  <=> v2_waybel_7(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f76,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f75,plain,(
    v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f74,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f71,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f69,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f68,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f67,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f2386,plain,(
    r2_hidden(k4_yellow_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f145,f67,f68,f69,f156,f73,f74,f75,f76,f77,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | r2_hidden(k4_yellow_0(X0),X1)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => r2_hidden(k4_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_4)).

fof(f156,plain,(
    v2_yellow_0(sK0) ),
    inference(unit_resulting_resolution,[],[f73,f154,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v2_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_0)).

fof(f154,plain,(
    v3_yellow_0(sK0) ),
    inference(unit_resulting_resolution,[],[f73,f145,f70,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v11_waybel_1(X0)
      | v3_yellow_0(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc8_waybel_1)).

fof(f6222,plain,
    ( spl9_1
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f6221])).

fof(f6221,plain,
    ( $false
    | spl9_1
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f2602,f6220])).

fof(f6220,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | spl9_1
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f6181,f3619])).

fof(f3619,plain,
    ( k3_yellow_0(sK0) = k12_lattice3(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f145,f70,f73,f2673,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v11_waybel_1(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k12_lattice3(X0,X1,k7_waybel_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2673,plain,
    ( m1_subset_1(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),u1_struct_0(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f77,f2670,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f2670,plain,
    ( r2_hidden(k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),sK1)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f67,f68,f69,f71,f73,f74,f125,f75,f76,f77,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(k13_lattice3(X0,sK5(X0,X1),sK6(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f125,plain,
    ( ~ v2_waybel_7(sK1,sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f6181,plain,
    ( r2_hidden(k12_lattice3(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)),k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1)))),sK1)
    | spl9_1
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f69,f72,f73,f75,f76,f2670,f2673,f77,f2698,f3676,f114])).

fof(f114,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ~ r2_hidden(k12_lattice3(X0,sK7(X0,X1),sK8(X0,X1)),X1)
                & r2_hidden(sK8(X0,X1),X1)
                & r2_hidden(sK7(X0,X1),X1)
                & m1_subset_1(sK8(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f63,f65,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k12_lattice3(X0,sK7(X0,X1),X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK7(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k12_lattice3(X0,sK7(X0,X1),X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(sK7(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k12_lattice3(X0,sK7(X0,X1),sK8(X0,X1)),X1)
        & r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f3676,plain,
    ( m1_subset_1(k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))),u1_struct_0(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f145,f73,f2673,f120])).

fof(f2698,plain,
    ( r2_hidden(k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))),sK1)
    | spl9_1
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f2683,f2567])).

fof(f2567,plain,
    ( k7_waybel_1(sK0,k13_lattice3(sK0,sK5(sK0,sK1),sK6(sK0,sK1))) = k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1)))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f145,f70,f73,f2450,f2549,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v11_waybel_1(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_waybel_1(X0,k12_lattice3(X0,X1,X2)) = k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2))
                & k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k7_waybel_1(X0,k12_lattice3(X0,X1,X2)) = k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2))
                & k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v11_waybel_1(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k7_waybel_1(X0,k12_lattice3(X0,X1,X2)) = k13_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2))
                & k7_waybel_1(X0,k13_lattice3(X0,X1,X2)) = k12_lattice3(X0,k7_waybel_1(X0,X1),k7_waybel_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_5)).

fof(f2549,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f67,f68,f69,f71,f73,f74,f125,f75,f76,f77,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2450,plain,
    ( m1_subset_1(sK5(sK0,sK1),u1_struct_0(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f67,f68,f69,f71,f73,f74,f125,f75,f76,f77,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | v2_waybel_7(X1,X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2683,plain,
    ( r2_hidden(k12_lattice3(sK0,k7_waybel_1(sK0,sK5(sK0,sK1)),k7_waybel_1(sK0,sK6(sK0,sK1))),sK1)
    | spl9_1
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f69,f72,f73,f75,f76,f2453,f2477,f2552,f2585,f77,f114])).

fof(f2585,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK6(sK0,sK1)),u1_struct_0(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f145,f73,f2549,f120])).

fof(f2552,plain,
    ( r2_hidden(k7_waybel_1(sK0,sK6(sK0,sK1)),sK1)
    | spl9_1
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f2447,f2549,f143])).

fof(f143,plain,
    ( ! [X3] :
        ( r2_hidden(k7_waybel_1(sK0,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,sK1) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_5
  <=> ! [X3] :
        ( r2_hidden(k7_waybel_1(sK0,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f2447,plain,
    ( ~ r2_hidden(sK6(sK0,sK1),sK1)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f67,f68,f69,f71,f73,f74,f75,f76,f125,f77,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2477,plain,
    ( m1_subset_1(k7_waybel_1(sK0,sK5(sK0,sK1)),u1_struct_0(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f145,f73,f2450,f120])).

fof(f2453,plain,
    ( r2_hidden(k7_waybel_1(sK0,sK5(sK0,sK1)),sK1)
    | spl9_1
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f2415,f2450,f143])).

fof(f2415,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f67,f68,f69,f71,f73,f74,f75,f76,f125,f77,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | v2_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f2602,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f73,f76,f2447,f77,f146,f2549,f2584,f96])).

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
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).

fof(f54,plain,(
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

fof(f55,plain,(
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

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f2584,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK6(sK0,sK1))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f145,f69,f157,f73,f2549,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f157,plain,(
    v1_yellow_0(sK0) ),
    inference(unit_resulting_resolution,[],[f73,f154,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v1_yellow_0(X0)
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f146,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f73,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f144,plain,
    ( spl9_1
    | spl9_5 ),
    inference(avatar_split_clause,[],[f78,f142,f123])).

fof(f78,plain,(
    ! [X3] :
      ( r2_hidden(k7_waybel_1(sK0,X3),sK1)
      | r2_hidden(X3,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | v2_waybel_7(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f140,plain,
    ( ~ spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f79,f137,f123])).

fof(f79,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f135,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f80,f132,f123])).

fof(f80,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f130,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f81,f127,f123])).

fof(f81,plain,
    ( ~ r2_hidden(k7_waybel_1(sK0,sK2),sK1)
    | ~ v2_waybel_7(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

%------------------------------------------------------------------------------
