%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 148 expanded)
%              Number of leaves         :   16 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  315 ( 774 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(resolution,[],[f107,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f107,plain,(
    v2_struct_0(sK0) ),
    inference(resolution,[],[f102,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f99,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f5,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f99,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f97,f77])).

fof(f77,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f70,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f70,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( X0 != X0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f61,f68])).

fof(f68,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f66,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(resolution,[],[f62,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f59,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,X0)),k1_xboole_0)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,X0)),k1_xboole_0)
      | v2_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f95,f90])).

fof(f90,plain,
    ( r2_waybel_0(sK0,sK1,k1_xboole_0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f89,f43])).

fof(f43,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | r2_waybel_0(sK0,sK1,k1_xboole_0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f88,f68])).

fof(f88,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0))
      | v2_struct_0(sK1)
      | r2_waybel_0(sK0,sK1,X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f87,f42])).

fof(f42,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X0,sK0)
      | r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
      | v2_struct_0(X0)
      | r2_waybel_0(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_waybel_0(sK0,sK1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | v2_struct_0(sK1)
      | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f94,f42])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,sK0)
      | ~ r2_waybel_0(sK0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | r2_hidden(k2_waybel_0(sK0,X1,sK3(sK0,X1,X2,X0)),X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f49,f38])).

fof(f49,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
                      & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (20718)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.42  % (20718)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f108,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(resolution,[],[f107,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ~v2_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & v7_waybel_0(sK1) & v4_orders_2(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f9])).
% 0.21/0.42  fof(f9,conjecture,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    v2_struct_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f102,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ~v2_struct_0(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f99,f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(sK5(X0),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ! [X0] : m1_subset_1(sK5(X0),X0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f5,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK5(X0),X0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK1)) | v2_struct_0(sK1) | v2_struct_0(sK0)) )),
% 0.21/0.42    inference(resolution,[],[f97,f77])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(condensation,[],[f75])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(resolution,[],[f70,f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(rectify,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f69])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    ( ! [X0] : (X0 != X0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(superposition,[],[f61,f68])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(resolution,[],[f66,f44])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | k6_subset_1(X0,X1) = X0) )),
% 0.21/0.42    inference(resolution,[],[f62,f65])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.21/0.42    inference(resolution,[],[f57,f52])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(rectify,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f35])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 0.21/0.42    inference(definition_unfolding,[],[f59,f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k6_subset_1(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f60,f55])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f36])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,X0)),k1_xboole_0) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK0)) )),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f96])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v2_struct_0(sK1) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,X0)),k1_xboole_0) | v2_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0)) )),
% 0.21/0.42    inference(resolution,[],[f95,f90])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    r2_waybel_0(sK0,sK1,k1_xboole_0) | v2_struct_0(sK1) | v2_struct_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f89,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,k1_xboole_0) | v2_struct_0(sK0)),
% 0.21/0.42    inference(superposition,[],[f88,f68])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    ( ! [X0] : (r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0)) | v2_struct_0(sK1) | r2_waybel_0(sK0,sK1,X0) | v2_struct_0(sK0)) )),
% 0.21/0.42    inference(resolution,[],[f87,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    l1_waybel_0(sK1,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | v2_struct_0(X0) | r2_waybel_0(sK0,X0,X1) | v2_struct_0(sK0)) )),
% 0.21/0.42    inference(resolution,[],[f46,f38])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    l1_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f21])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(nnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_waybel_0(sK0,sK1,X0) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v2_struct_0(sK1) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0) | v2_struct_0(sK0)) )),
% 0.21/0.42    inference(resolution,[],[f94,f42])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,sK0) | ~r2_waybel_0(sK0,X1,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | r2_hidden(k2_waybel_0(sK0,X1,sK3(sK0,X1,X2,X0)),X2) | v2_struct_0(sK0)) )),
% 0.21/0.42    inference(resolution,[],[f49,f38])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X2,X0,X5,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | v2_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f24,f26,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(rectify,[],[f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(nnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (20718)------------------------------
% 0.21/0.42  % (20718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (20718)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (20718)Memory used [KB]: 1663
% 0.21/0.42  % (20718)Time elapsed: 0.007 s
% 0.21/0.42  % (20718)------------------------------
% 0.21/0.42  % (20718)------------------------------
% 0.21/0.42  % (20716)Success in time 0.068 s
%------------------------------------------------------------------------------
