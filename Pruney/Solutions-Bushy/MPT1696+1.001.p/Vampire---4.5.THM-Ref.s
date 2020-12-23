%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1696+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:21 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  260 (3364 expanded)
%              Number of leaves         :   26 (1015 expanded)
%              Depth                    :   31
%              Number of atoms          : 1782 (31606 expanded)
%              Number of equality atoms :   41 ( 324 expanded)
%              Maximal formula depth    :   15 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f91,f112,f258,f270,f326,f334,f342,f346,f363,f367,f460,f579,f593,f621,f650,f656])).

fof(f656,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_18
    | spl9_19
    | spl9_21
    | ~ spl9_27 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_18
    | spl9_19
    | spl9_21
    | ~ spl9_27 ),
    inference(global_subsumption,[],[f652,f332])).

fof(f332,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | spl9_19 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl9_19
  <=> r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f652,plain,
    ( r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_18
    | spl9_21
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f651,f301])).

fof(f301,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f300,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ( ~ r2_yellow_0(sK0,sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(sK1) )
      | ~ v25_waybel_0(sK0) )
    & ( ! [X2] :
          ( r2_yellow_0(sK0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
          | v1_xboole_0(X2) )
      | v25_waybel_0(sK0) )
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_yellow_0(X0,X1)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
          | ~ v25_waybel_0(X0) )
        & ( ! [X2] :
              ( r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X2) )
          | v25_waybel_0(X0) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ? [X1] :
            ( ~ r2_yellow_0(sK0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(sK0) )
      & ( ! [X2] :
            ( r2_yellow_0(sK0,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
            | v1_xboole_0(X2) )
        | v25_waybel_0(sK0) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ r2_yellow_0(sK0,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ~ r2_yellow_0(sK0,sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(X0) )
      & ( ! [X2] :
            ( r2_yellow_0(X0,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X2) )
        | v25_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(X0) )
      & ( ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) )
        | v25_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_yellow_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        | ~ v25_waybel_0(X0) )
      & ( ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) )
        | v25_waybel_0(X0) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ( v25_waybel_0(X0)
      <~> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( v25_waybel_0(X0)
      <~> ! [X1] :
            ( r2_yellow_0(X0,X1)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v25_waybel_0(X0)
        <=> ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & ~ v1_xboole_0(X1) )
             => r2_yellow_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => r2_yellow_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_waybel_0)).

fof(f300,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f299,f35])).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f299,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f298,f37])).

fof(f37,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f298,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f297,f71])).

fof(f71,plain,
    ( v25_waybel_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl9_1
  <=> v25_waybel_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f297,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f291,f86])).

fof(f86,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl9_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f291,plain,
    ( m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f81,f60])).

fof(f60,plain,(
    ! [X4,X0] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK8(X0,X4),u1_struct_0(X0))
      | v1_xboole_0(X4)
      | ~ v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v25_waybel_0(X0)
          | ( ! [X2] :
                ( ( ~ r1_orders_2(X0,sK7(X0,X2),X2)
                  & r1_lattice3(X0,sK6(X0),sK7(X0,X2))
                  & m1_subset_1(sK7(X0,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,sK6(X0),X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(sK6(X0)) ) )
        & ( ! [X4] :
              ( ( ! [X6] :
                    ( r1_orders_2(X0,X6,sK8(X0,X4))
                    | ~ r1_lattice3(X0,X4,X6)
                    | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                & r1_lattice3(X0,X4,sK8(X0,X4))
                & m1_subset_1(sK8(X0,X4),u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X4) )
          | ~ v25_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(X0,X3,X2)
                & r1_lattice3(X0,sK6(X0),X3)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,sK6(X0),X2)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,sK6(X0),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK7(X0,X2),X2)
        & r1_lattice3(X0,sK6(X0),sK7(X0,X2))
        & m1_subset_1(sK7(X0,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X4,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r1_orders_2(X0,X6,X5)
              | ~ r1_lattice3(X0,X4,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & r1_lattice3(X0,X4,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r1_orders_2(X0,X6,sK8(X0,X4))
            | ~ r1_lattice3(X0,X4,X6)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & r1_lattice3(X0,X4,sK8(X0,X4))
        & m1_subset_1(sK8(X0,X4),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v25_waybel_0(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X2)
                      & r1_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X4] :
              ( ? [X5] :
                  ( ! [X6] :
                      ( r1_orders_2(X0,X6,X5)
                      | ~ r1_lattice3(X0,X4,X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X4,X5)
                  & m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X4) )
          | ~ v25_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v25_waybel_0(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X2)
                      & r1_lattice3(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X2)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( r1_orders_2(X0,X3,X2)
                      | ~ r1_lattice3(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | v1_xboole_0(X1) )
          | ~ v25_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | v1_xboole_0(X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v25_waybel_0(X0)
      <=> ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ? [X2] :
                ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d40_waybel_0)).

fof(f81,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl9_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f651,plain,
    ( r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_18
    | spl9_21
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f564,f625])).

fof(f625,plain,
    ( ~ r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_18
    | spl9_21
    | ~ spl9_27 ),
    inference(global_subsumption,[],[f362,f325,f624])).

fof(f624,plain,
    ( sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1))
    | ~ r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f623,f36])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f623,plain,
    ( sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1))
    | ~ r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f622,f37])).

fof(f622,plain,
    ( sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1))
    | ~ r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f603,f301])).

fof(f603,plain,
    ( sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1))
    | ~ r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl9_27 ),
    inference(resolution,[],[f459,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f459,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f457])).

fof(f457,plain,
    ( spl9_27
  <=> r1_orders_2(sK0,sK2(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f325,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl9_18
  <=> m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f362,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | spl9_21 ),
    inference(avatar_component_clause,[],[f360])).

fof(f360,plain,
    ( spl9_21
  <=> sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f564,plain,
    ( r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f352,f296])).

fof(f296,plain,
    ( r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f295,f34])).

fof(f295,plain,
    ( r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f294,f35])).

fof(f294,plain,
    ( r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f293,f37])).

fof(f293,plain,
    ( r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f292,f71])).

fof(f292,plain,
    ( r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f290,f86])).

fof(f290,plain,
    ( r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    ! [X4,X0] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_lattice3(X0,X4,sK8(X0,X4))
      | v1_xboole_0(X4)
      | ~ v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f352,plain,
    ( ! [X1] :
        ( ~ r1_lattice3(sK0,sK1,X1)
        | r1_lattice3(sK0,sK1,sK3(sK0,sK1,X1))
        | r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f351,f37])).

fof(f351,plain,
    ( ! [X1] :
        ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X1))
        | r1_lattice3(sK0,sK1,sK3(sK0,sK1,X1))
        | ~ r1_lattice3(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f350,f301])).

fof(f350,plain,
    ( ! [X1] :
        ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X1))
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | r1_lattice3(sK0,sK1,sK3(sK0,sK1,X1))
        | ~ r1_lattice3(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f310,f76])).

fof(f76,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl9_2
  <=> r2_yellow_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f310,plain,
    ( ! [X1] :
        ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X1))
        | r2_yellow_0(sK0,sK1)
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | r1_lattice3(sK0,sK1,sK3(sK0,sK1,X1))
        | ~ r1_lattice3(sK0,sK1,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f296,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( sK2(X0,X1,X2) != X2
                  & ! [X4] :
                      ( r1_orders_2(X0,X4,sK2(X0,X1,X2))
                      | ~ r1_lattice3(X0,X1,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X1,sK2(X0,X1,X2))
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X7] :
                  ( sK4(X0,X1) = X7
                  | ( ~ r1_orders_2(X0,sK5(X0,X1,X7),X7)
                    & r1_lattice3(X0,X1,sK5(X0,X1,X7))
                    & m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X7)
                  | ~ m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X9] :
                  ( r1_orders_2(X0,X9,sK4(X0,X1))
                  | ~ r1_lattice3(X0,X1,X9)
                  | ~ m1_subset_1(X9,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK4(X0,X1))
              & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f26,f25,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( X2 != X3
          & ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_lattice3(X0,X1,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK2(X0,X1,X2) != X2
        & ! [X4] :
            ( r1_orders_2(X0,X4,sK2(X0,X1,X2))
            | ~ r1_lattice3(X0,X1,X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK2(X0,X1,X2))
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ~ r1_orders_2(X0,X5,X2)
          & r1_lattice3(X0,X1,X5)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X6] :
          ( ! [X7] :
              ( X6 = X7
              | ? [X8] :
                  ( ~ r1_orders_2(X0,X8,X7)
                  & r1_lattice3(X0,X1,X8)
                  & m1_subset_1(X8,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X7)
              | ~ m1_subset_1(X7,u1_struct_0(X0)) )
          & ! [X9] :
              ( r1_orders_2(X0,X9,X6)
              | ~ r1_lattice3(X0,X1,X9)
              | ~ m1_subset_1(X9,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( ! [X7] :
            ( sK4(X0,X1) = X7
            | ? [X8] :
                ( ~ r1_orders_2(X0,X8,X7)
                & r1_lattice3(X0,X1,X8)
                & m1_subset_1(X8,u1_struct_0(X0)) )
            | ~ r1_lattice3(X0,X1,X7)
            | ~ m1_subset_1(X7,u1_struct_0(X0)) )
        & ! [X9] :
            ( r1_orders_2(X0,X9,sK4(X0,X1))
            | ~ r1_lattice3(X0,X1,X9)
            | ~ m1_subset_1(X9,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X7,X1,X0] :
      ( ? [X8] :
          ( ~ r1_orders_2(X0,X8,X7)
          & r1_lattice3(X0,X1,X8)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X7),X7)
        & r1_lattice3(X0,X1,sK5(X0,X1,X7))
        & m1_subset_1(sK5(X0,X1,X7),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (27331)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X5,X2)
                    & r1_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X6] :
                ( ! [X7] :
                    ( X6 = X7
                    | ? [X8] :
                        ( ~ r1_orders_2(X0,X8,X7)
                        & r1_lattice3(X0,X1,X8)
                        & m1_subset_1(X8,u1_struct_0(X0)) )
                    | ~ r1_lattice3(X0,X1,X7)
                    | ~ m1_subset_1(X7,u1_struct_0(X0)) )
                & ! [X9] :
                    ( r1_orders_2(X0,X9,X6)
                    | ~ r1_lattice3(X0,X1,X9)
                    | ~ m1_subset_1(X9,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X6)
                & m1_subset_1(X6,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( X2 != X3
                    & ! [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        | ~ r1_lattice3(X0,X1,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ? [X5] :
                    ( ~ r1_orders_2(X0,X5,X2)
                    & r1_lattice3(X0,X1,X5)
                    & m1_subset_1(X5,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( X2 = X3
                    | ? [X4] :
                        ( ~ r1_orders_2(X0,X4,X3)
                        & r1_lattice3(X0,X1,X4)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & ! [X5] :
                    ( r1_orders_2(X0,X5,X2)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( X2 = X3
                  | ? [X4] :
                      ( ~ r1_orders_2(X0,X4,X3)
                      & r1_lattice3(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & ! [X5] :
                  ( r1_orders_2(X0,X5,X2)
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X5] :
                  ( m1_subset_1(X5,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X5)
                   => r1_orders_2(X0,X5,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_lattice3(X0,X1,X4)
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_lattice3(X0,X1,X3) )
                   => X2 = X3 ) )
              & ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_0)).

fof(f650,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_17
    | ~ spl9_18
    | spl9_21
    | ~ spl9_27 ),
    inference(avatar_contradiction_clause,[],[f649])).

fof(f649,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | spl9_17
    | ~ spl9_18
    | spl9_21
    | ~ spl9_27 ),
    inference(global_subsumption,[],[f627,f320])).

fof(f320,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | spl9_17 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl9_17
  <=> m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f627,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_18
    | spl9_21
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f626,f301])).

fof(f626,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_18
    | spl9_21
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f561,f625])).

fof(f561,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f349,f296])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK1,X0)
        | m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f348,f37])).

fof(f348,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X0))
        | m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f347,f301])).

fof(f347,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X0))
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f309,f76])).

fof(f309,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X0))
        | r2_yellow_0(sK0,sK1)
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | m1_subset_1(sK3(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f296,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f621,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f619,f37])).

fof(f619,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f618,f301])).

fof(f618,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f617,f296])).

fof(f617,plain,
    ( ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f616,f76])).

fof(f616,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f570,f615])).

fof(f615,plain,
    ( sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f614,f36])).

fof(f614,plain,
    ( sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1))
    | ~ v5_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f613,f37])).

fof(f613,plain,
    ( sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f612,f301])).

fof(f612,plain,
    ( sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f611,f587])).

fof(f587,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f586,f37])).

fof(f586,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f585,f301])).

fof(f585,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f584,f296])).

fof(f584,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f569,f76])).

fof(f569,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(resolution,[],[f560,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f560,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f559,f34])).

fof(f559,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f558,f35])).

fof(f558,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f557,f37])).

fof(f557,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f556,f71])).

fof(f556,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f555,f86])).

fof(f555,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f554,f81])).

fof(f554,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f500,f321])).

fof(f321,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f319])).

fof(f500,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_19 ),
    inference(resolution,[],[f333,f62])).

fof(f62,plain,(
    ! [X6,X4,X0] :
      ( ~ r1_lattice3(X0,X4,X6)
      | r1_orders_2(X0,X6,sK8(X0,X4))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X4)
      | ~ v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f333,plain,
    ( r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f331])).

fof(f611,plain,
    ( sK8(sK0,sK1) = sK2(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f603,f573])).

fof(f573,plain,
    ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f572,f301])).

fof(f572,plain,
    ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f567,f296])).

fof(f567,plain,
    ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(resolution,[],[f560,f355])).

fof(f355,plain,
    ( ! [X2] :
        ( ~ r1_orders_2(sK0,sK3(sK0,sK1,X2),X2)
        | r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X2))
        | ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f354,f37])).

fof(f354,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X2))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1,X2),X2)
        | ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f353,f301])).

fof(f353,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X2))
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1,X2),X2)
        | ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f311,f76])).

fof(f311,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,sK8(sK0,sK1),sK2(sK0,sK1,X2))
        | r2_yellow_0(sK0,sK1)
        | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK3(sK0,sK1,X2),X2)
        | ~ r1_lattice3(sK0,sK1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f296,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X4)
      | r1_orders_2(X0,X4,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f570,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(resolution,[],[f560,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | sK2(X0,X1,X2) != X2
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f593,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | spl9_20 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19
    | spl9_20 ),
    inference(subsumption_resolution,[],[f340,f591])).

fof(f591,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f590,f37])).

fof(f590,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f589,f301])).

fof(f589,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f588,f296])).

fof(f588,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f568,f76])).

fof(f568,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(resolution,[],[f560,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f340,plain,
    ( ~ r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | spl9_20 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl9_20
  <=> r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f579,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | spl9_18
    | ~ spl9_19 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | spl9_18
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f577,f37])).

fof(f577,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | spl9_18
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f576,f301])).

fof(f576,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | spl9_18
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f575,f296])).

fof(f575,plain,
    ( ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | spl9_18
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f574,f76])).

fof(f574,plain,
    ( r2_yellow_0(sK0,sK1)
    | ~ r1_lattice3(sK0,sK1,sK8(sK0,sK1))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_17
    | spl9_18
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f569,f324])).

fof(f324,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | spl9_18 ),
    inference(avatar_component_clause,[],[f323])).

fof(f460,plain,
    ( ~ spl9_18
    | spl9_27
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f455,f339,f84,f79,f70,f457,f323])).

fof(f455,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f454,f34])).

fof(f454,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f453,f35])).

fof(f453,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f452,f37])).

fof(f452,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f451,f71])).

fof(f451,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | spl9_4
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f450,f86])).

fof(f450,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f389,f81])).

fof(f389,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1,sK8(sK0,sK1)),sK8(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_20 ),
    inference(resolution,[],[f341,f62])).

fof(f341,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f339])).

fof(f367,plain,
    ( spl9_19
    | ~ spl9_21
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f366,f84,f79,f74,f70,f360,f331])).

fof(f366,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f365,f37])).

fof(f365,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f364,f301])).

fof(f364,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f313,f76])).

fof(f313,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f296,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | sK2(X0,X1,X2) != X2
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f363,plain,
    ( spl9_17
    | ~ spl9_21
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f358,f84,f79,f74,f70,f360,f319])).

fof(f358,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f357,f37])).

fof(f357,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f356,f301])).

fof(f356,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f312,f76])).

fof(f312,plain,
    ( sK8(sK0,sK1) != sK2(sK0,sK1,sK8(sK0,sK1))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f296,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | sK2(X0,X1,X2) != X2
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f346,plain,
    ( spl9_19
    | spl9_20
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f345,f84,f79,f74,f70,f339,f331])).

fof(f345,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f344,f37])).

fof(f344,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f343,f301])).

fof(f343,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f308,f76])).

fof(f308,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f296,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f342,plain,
    ( spl9_17
    | spl9_20
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f337,f84,f79,f74,f70,f339,f319])).

fof(f337,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f336,f37])).

fof(f336,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f335,f301])).

fof(f335,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f307,f76])).

fof(f307,plain,
    ( r1_lattice3(sK0,sK1,sK2(sK0,sK1,sK8(sK0,sK1)))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f296,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,X1,sK2(X0,X1,X2))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f334,plain,
    ( spl9_19
    | spl9_18
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f329,f84,f79,f74,f70,f323,f331])).

fof(f329,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f328,f37])).

fof(f328,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f327,f301])).

fof(f327,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f306,f76])).

fof(f306,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3(sK0,sK1,sK8(sK0,sK1)))
    | r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f296,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f326,plain,
    ( spl9_17
    | spl9_18
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f317,f84,f79,f74,f70,f323,f319])).

fof(f317,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f316,f37])).

fof(f316,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f315,f301])).

fof(f315,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | spl9_2
    | ~ spl9_3
    | spl9_4 ),
    inference(subsumption_resolution,[],[f305,f76])).

fof(f305,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | m1_subset_1(sK3(sK0,sK1,sK8(sK0,sK1)),u1_struct_0(sK0))
    | r2_yellow_0(sK0,sK1)
    | ~ m1_subset_1(sK8(sK0,sK1),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_1
    | ~ spl9_3
    | spl9_4 ),
    inference(resolution,[],[f296,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f270,plain,
    ( spl9_1
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | spl9_1
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f268,f34])).

fof(f268,plain,
    ( v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f267,f35])).

fof(f267,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f266,f37])).

fof(f266,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f265,f72])).

fof(f72,plain,
    ( ~ v25_waybel_0(sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f265,plain,
    ( v25_waybel_0(sK0)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8 ),
    inference(resolution,[],[f264,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK6(X0))
      | v25_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f264,plain,
    ( v1_xboole_0(sK6(sK0))
    | ~ spl9_5
    | spl9_6
    | ~ spl9_8 ),
    inference(global_subsumption,[],[f99,f121])).

fof(f121,plain,
    ( v1_xboole_0(sK6(sK0))
    | r2_yellow_0(sK0,sK6(sK0))
    | ~ spl9_5
    | ~ spl9_8 ),
    inference(resolution,[],[f111,f90])).

fof(f90,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X2)
        | r2_yellow_0(sK0,X2) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl9_5
  <=> ! [X2] :
        ( r2_yellow_0(sK0,X2)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f111,plain,
    ( m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl9_8
  <=> m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f99,plain,
    ( ~ r2_yellow_0(sK0,sK6(sK0))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_6
  <=> r2_yellow_0(sK0,sK6(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f258,plain,
    ( spl9_1
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f256,f34])).

fof(f256,plain,
    ( v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f255,f35])).

fof(f255,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f254,f37])).

fof(f254,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f253,f120])).

fof(f120,plain,
    ( m1_subset_1(sK4(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f118,f37])).

fof(f118,plain,
    ( m1_subset_1(sK4(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f100,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f100,plain,
    ( r2_yellow_0(sK0,sK6(sK0))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f253,plain,
    ( ~ m1_subset_1(sK4(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f252,f119])).

fof(f119,plain,
    ( r1_lattice3(sK0,sK6(sK0),sK4(sK0,sK6(sK0)))
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f117,f37])).

fof(f117,plain,
    ( r1_lattice3(sK0,sK6(sK0),sK4(sK0,sK6(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f100,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,sK4(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f252,plain,
    ( ~ r1_lattice3(sK0,sK6(sK0),sK4(sK0,sK6(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f250,f72])).

fof(f250,plain,
    ( v25_waybel_0(sK0)
    | ~ r1_lattice3(sK0,sK6(sK0),sK4(sK0,sK6(sK0)))
    | ~ m1_subset_1(sK4(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(resolution,[],[f179,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ r1_orders_2(X0,sK7(X0,X2),X2)
      | v25_waybel_0(X0)
      | ~ r1_lattice3(X0,sK6(X0),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f179,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK4(sK0,sK6(sK0))),sK4(sK0,sK6(sK0)))
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f178,f37])).

fof(f178,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK4(sK0,sK6(sK0))),sK4(sK0,sK6(sK0)))
    | ~ l1_orders_2(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f177,f100])).

fof(f177,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK4(sK0,sK6(sK0))),sK4(sK0,sK6(sK0)))
    | ~ r2_yellow_0(sK0,sK6(sK0))
    | ~ l1_orders_2(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f154,f146])).

fof(f146,plain,
    ( m1_subset_1(sK7(sK0,sK4(sK0,sK6(sK0))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f145,f34])).

fof(f145,plain,
    ( m1_subset_1(sK7(sK0,sK4(sK0,sK6(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f144,f35])).

fof(f144,plain,
    ( m1_subset_1(sK7(sK0,sK4(sK0,sK6(sK0))),u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f143,f37])).

fof(f143,plain,
    ( m1_subset_1(sK7(sK0,sK4(sK0,sK6(sK0))),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f142,f120])).

fof(f142,plain,
    ( m1_subset_1(sK7(sK0,sK4(sK0,sK6(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f125,f72])).

fof(f125,plain,
    ( m1_subset_1(sK7(sK0,sK4(sK0,sK6(sK0))),u1_struct_0(sK0))
    | v25_waybel_0(sK0)
    | ~ m1_subset_1(sK4(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f119,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r1_lattice3(X0,sK6(X0),X2)
      | m1_subset_1(sK7(X0,X2),u1_struct_0(X0))
      | v25_waybel_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f154,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK4(sK0,sK6(sK0))),sK4(sK0,sK6(sK0)))
    | ~ m1_subset_1(sK7(sK0,sK4(sK0,sK6(sK0))),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,sK6(sK0))
    | ~ l1_orders_2(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(resolution,[],[f141,f44])).

fof(f44,plain,(
    ! [X0,X1,X9] :
      ( ~ r1_lattice3(X0,X1,X9)
      | r1_orders_2(X0,X9,sK4(X0,X1))
      | ~ m1_subset_1(X9,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,
    ( r1_lattice3(sK0,sK6(sK0),sK7(sK0,sK4(sK0,sK6(sK0))))
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f140,f34])).

fof(f140,plain,
    ( r1_lattice3(sK0,sK6(sK0),sK7(sK0,sK4(sK0,sK6(sK0))))
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f139,f35])).

fof(f139,plain,
    ( r1_lattice3(sK0,sK6(sK0),sK7(sK0,sK4(sK0,sK6(sK0))))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f138,f37])).

fof(f138,plain,
    ( r1_lattice3(sK0,sK6(sK0),sK7(sK0,sK4(sK0,sK6(sK0))))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f137,f120])).

fof(f137,plain,
    ( r1_lattice3(sK0,sK6(sK0),sK7(sK0,sK4(sK0,sK6(sK0))))
    | ~ m1_subset_1(sK4(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f124,f72])).

fof(f124,plain,
    ( r1_lattice3(sK0,sK6(sK0),sK7(sK0,sK4(sK0,sK6(sK0))))
    | v25_waybel_0(sK0)
    | ~ m1_subset_1(sK4(sK0,sK6(sK0)),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f119,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ r1_lattice3(X0,sK6(X0),X2)
      | r1_lattice3(X0,sK6(X0),sK7(X0,X2))
      | v25_waybel_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f112,plain,
    ( spl9_1
    | spl9_8 ),
    inference(avatar_split_clause,[],[f107,f109,f70])).

fof(f107,plain,
    ( m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v25_waybel_0(sK0) ),
    inference(subsumption_resolution,[],[f106,f34])).

fof(f106,plain,
    ( m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v25_waybel_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f92,f35])).

fof(f92,plain,
    ( m1_subset_1(sK6(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v25_waybel_0(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f64,f37])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v25_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,
    ( spl9_1
    | spl9_5 ),
    inference(avatar_split_clause,[],[f38,f89,f70])).

fof(f38,plain,(
    ! [X2] :
      ( r2_yellow_0(sK0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_xboole_0(X2)
      | v25_waybel_0(sK0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f87,plain,
    ( ~ spl9_1
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f39,f84,f70])).

fof(f39,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v25_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,
    ( ~ spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f40,f79,f70])).

fof(f40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v25_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f41,f74,f70])).

fof(f41,plain,
    ( ~ r2_yellow_0(sK0,sK1)
    | ~ v25_waybel_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
