%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t5_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:07 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 612 expanded)
%              Number of leaves         :   15 ( 149 expanded)
%              Depth                    :   17
%              Number of atoms          :  303 (3689 expanded)
%              Number of equality atoms :   42 ( 759 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f176,f219])).

fof(f219,plain,
    ( ~ spl6_0
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f189,f86])).

fof(f86,plain,
    ( k4_yellow_0(sK0) != k3_yellow_0(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_3
  <=> k4_yellow_0(sK0) != k3_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f189,plain,
    ( k4_yellow_0(sK0) = k3_yellow_0(sK0)
    | ~ spl6_0 ),
    inference(unit_resulting_resolution,[],[f92,f83,f96,f101,f65])).

fof(f65,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(X0))
      | X3 = X4
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ( sK1(X0) != sK2(X0)
            & m1_subset_1(sK2(X0),u1_struct_0(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK1(X0) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK2(X0) != X1
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( X3 = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( X1 = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ( v7_struct_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t5_waybel_7.p',d10_struct_0)).

fof(f101,plain,(
    m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f60,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t5_waybel_7.p',dt_k4_yellow_0)).

fof(f60,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k4_yellow_0(sK0) != k3_yellow_0(sK0)
      | ~ v7_struct_0(sK0) )
    & ( k4_yellow_0(sK0) = k3_yellow_0(sK0)
      | v7_struct_0(sK0) )
    & l1_orders_2(sK0)
    & v3_yellow_0(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ( k4_yellow_0(X0) != k3_yellow_0(X0)
          | ~ v7_struct_0(X0) )
        & ( k4_yellow_0(X0) = k3_yellow_0(X0)
          | v7_struct_0(X0) )
        & l1_orders_2(X0)
        & v3_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k4_yellow_0(sK0) != k3_yellow_0(sK0)
        | ~ v7_struct_0(sK0) )
      & ( k4_yellow_0(sK0) = k3_yellow_0(sK0)
        | v7_struct_0(sK0) )
      & l1_orders_2(sK0)
      & v3_yellow_0(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ( k4_yellow_0(X0) != k3_yellow_0(X0)
        | ~ v7_struct_0(X0) )
      & ( k4_yellow_0(X0) = k3_yellow_0(X0)
        | v7_struct_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ( k4_yellow_0(X0) != k3_yellow_0(X0)
        | ~ v7_struct_0(X0) )
      & ( k4_yellow_0(X0) = k3_yellow_0(X0)
        | v7_struct_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ( v7_struct_0(X0)
      <~> k4_yellow_0(X0) = k3_yellow_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ( v7_struct_0(X0)
      <~> k4_yellow_0(X0) = k3_yellow_0(X0) )
      & l1_orders_2(X0)
      & v3_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_struct_0(X0)
        <=> k4_yellow_0(X0) = k3_yellow_0(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> k4_yellow_0(X0) = k3_yellow_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t5_waybel_7.p',t5_waybel_7)).

fof(f96,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f60,f63])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t5_waybel_7.p',dt_k3_yellow_0)).

fof(f83,plain,
    ( v7_struct_0(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_0
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f92,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f60,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t5_waybel_7.p',dt_l1_orders_2)).

fof(f176,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f137,f109])).

fof(f109,plain,
    ( r1_orders_2(sK0,sK1(sK0),k4_yellow_0(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f57,f58,f95,f60,f103,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,k4_yellow_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t5_waybel_7.p',t45_yellow_0)).

fof(f103,plain,
    ( m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f92,f91,f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f62,f89])).

fof(f89,plain,
    ( k4_yellow_0(sK0) = k3_yellow_0(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_2
  <=> k4_yellow_0(sK0) = k3_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f62,plain,
    ( k4_yellow_0(sK0) != k3_yellow_0(sK0)
    | ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    v2_yellow_0(sK0) ),
    inference(unit_resulting_resolution,[],[f59,f60,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v3_yellow_0(X0)
      | v2_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_yellow_0(X0) )
      | ~ v3_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_yellow_0(X0)
       => ( v2_yellow_0(X0)
          & v1_yellow_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t5_waybel_7.p',cc4_yellow_0)).

fof(f59,plain,(
    v3_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f137,plain,
    ( ~ r1_orders_2(sK0,sK1(sK0),k4_yellow_0(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f58,f60,f99,f103,f125,f118,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t5_waybel_7.p',t25_orders_2)).

fof(f118,plain,
    ( r1_orders_2(sK0,k4_yellow_0(sK0),sK1(sK0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f113,f89])).

fof(f113,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK1(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f57,f58,f94,f60,f103,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t5_waybel_7.p',t44_yellow_0)).

fof(f94,plain,(
    v1_yellow_0(sK0) ),
    inference(unit_resulting_resolution,[],[f59,f60,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | ~ v3_yellow_0(X0)
      | v1_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f125,plain,
    ( k4_yellow_0(sK0) != sK1(sK0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f121,f105])).

fof(f105,plain,
    ( sK1(sK0) != sK2(sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f92,f91,f68])).

fof(f68,plain,(
    ! [X0] :
      ( sK1(X0) != sK2(X0)
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f121,plain,
    ( k4_yellow_0(sK0) = sK2(sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f58,f60,f99,f104,f110,f117,f77])).

fof(f117,plain,
    ( r1_orders_2(sK0,k4_yellow_0(sK0),sK2(sK0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f114,f89])).

fof(f114,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK2(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f57,f58,f94,f60,f104,f76])).

fof(f110,plain,
    ( r1_orders_2(sK0,sK2(sK0),k4_yellow_0(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f57,f58,f95,f60,f104,f75])).

fof(f104,plain,
    ( m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f92,f91,f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,
    ( m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f96,f89])).

fof(f90,plain,
    ( spl6_0
    | spl6_2 ),
    inference(avatar_split_clause,[],[f61,f88,f82])).

fof(f61,plain,
    ( k4_yellow_0(sK0) = k3_yellow_0(sK0)
    | v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
