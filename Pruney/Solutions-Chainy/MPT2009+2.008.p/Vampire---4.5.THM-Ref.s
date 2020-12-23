%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:02 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 196 expanded)
%              Number of leaves         :   15 (  55 expanded)
%              Depth                    :   30
%              Number of atoms          :  449 (1026 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(subsumption_resolution,[],[f94,f45])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1)))
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1)))
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

fof(f94,plain,(
    ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f93,f47])).

fof(f47,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f92,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f92,plain,(
    ~ l1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f91,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f90,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ~ v2_struct_0(sK4(X0))
        & l1_waybel_0(sK4(X0),X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
     => ( ~ v2_struct_0(sK4(X0))
        & l1_waybel_0(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v6_waybel_0(X1,X0)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v6_waybel_0(X1,X0)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_yellow_6(X1,X0)
          & v7_waybel_0(X1)
          & v6_waybel_0(X1,X0)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_yellow_6)).

fof(f90,plain,(
    ! [X0] : ~ l1_waybel_0(X0,sK1) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f89,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | ~ l1_waybel_0(X0,sK1) ) ),
    inference(resolution,[],[f88,f47])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK1,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_waybel_0(X0,sK1) ) ),
    inference(resolution,[],[f86,f65])).

fof(f86,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK1)
      | ~ l1_waybel_0(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(X0,sK1)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f82,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(f82,plain,(
    ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f81,f47])).

fof(f81,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f80,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f79,f45])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f78,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ l1_waybel_0(sK1,sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f77,f48])).

fof(f48,plain,(
    ~ r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f76,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3))
                      & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK3(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3))
        & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK3(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f74,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2)
      | r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X2,X1,X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f73,f65])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X2,X1,X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))
      | ~ l1_waybel_0(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | r2_hidden(k2_waybel_0(X2,X1,X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1)))
      | ~ l1_waybel_0(X1,X2)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X2)
      | v2_struct_0(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f71,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f70,f52])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f69,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ v1_funct_1(u1_waybel_0(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f68,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

% (22426)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% (22426)Refutation not found, incomplete strategy% (22426)------------------------------
% (22426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22426)Termination reason: Refutation not found, incomplete strategy

% (22426)Memory used [KB]: 10618
% (22426)Time elapsed: 0.072 s
% (22426)------------------------------
% (22426)------------------------------
% (22424)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% (22425)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% (22440)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (22440)Refutation not found, incomplete strategy% (22440)------------------------------
% (22440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22440)Termination reason: Refutation not found, incomplete strategy

% (22440)Memory used [KB]: 1535
% (22440)Time elapsed: 0.001 s
% (22440)------------------------------
% (22440)------------------------------
% (22444)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% (22432)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(u1_waybel_0(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f67,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(u1_waybel_0(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0)))
      | ~ m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(u1_waybel_0(X1,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f49,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:58:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (803831809)
% 0.14/0.37  ipcrm: permission denied for id (803864578)
% 0.14/0.37  ipcrm: permission denied for id (803930116)
% 0.14/0.37  ipcrm: permission denied for id (803995654)
% 0.14/0.38  ipcrm: permission denied for id (804028425)
% 0.14/0.38  ipcrm: permission denied for id (804061194)
% 0.14/0.38  ipcrm: permission denied for id (804159501)
% 0.14/0.39  ipcrm: permission denied for id (804225041)
% 0.14/0.39  ipcrm: permission denied for id (804257811)
% 0.14/0.39  ipcrm: permission denied for id (804323351)
% 0.14/0.40  ipcrm: permission denied for id (804421659)
% 0.14/0.40  ipcrm: permission denied for id (804454428)
% 0.14/0.40  ipcrm: permission denied for id (804487197)
% 0.21/0.40  ipcrm: permission denied for id (804519967)
% 0.21/0.40  ipcrm: permission denied for id (804552736)
% 0.21/0.42  ipcrm: permission denied for id (804618286)
% 0.21/0.42  ipcrm: permission denied for id (804651056)
% 0.21/0.43  ipcrm: permission denied for id (804683826)
% 0.21/0.43  ipcrm: permission denied for id (804847671)
% 0.21/0.44  ipcrm: permission denied for id (804945981)
% 0.21/0.44  ipcrm: permission denied for id (804978751)
% 0.21/0.45  ipcrm: permission denied for id (805109829)
% 0.21/0.45  ipcrm: permission denied for id (805240905)
% 0.21/0.46  ipcrm: permission denied for id (805404753)
% 0.21/0.47  ipcrm: permission denied for id (805437524)
% 0.21/0.48  ipcrm: permission denied for id (805634145)
% 0.21/0.49  ipcrm: permission denied for id (805732454)
% 0.21/0.50  ipcrm: permission denied for id (805830764)
% 0.21/0.50  ipcrm: permission denied for id (805863533)
% 0.21/0.50  ipcrm: permission denied for id (805896303)
% 0.21/0.50  ipcrm: permission denied for id (805929072)
% 0.21/0.51  ipcrm: permission denied for id (805994612)
% 0.21/0.51  ipcrm: permission denied for id (806027381)
% 0.21/0.51  ipcrm: permission denied for id (806092919)
% 0.21/0.51  ipcrm: permission denied for id (806125688)
% 0.21/0.52  ipcrm: permission denied for id (806191231)
% 0.95/0.62  % (22428)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.95/0.63  % (22435)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.95/0.63  % (22437)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.95/0.64  % (22431)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.95/0.64  % (22431)Refutation not found, incomplete strategy% (22431)------------------------------
% 0.95/0.64  % (22431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.95/0.64  % (22431)Termination reason: Refutation not found, incomplete strategy
% 0.95/0.64  
% 0.95/0.64  % (22431)Memory used [KB]: 6012
% 0.95/0.64  % (22431)Time elapsed: 0.001 s
% 0.95/0.64  % (22431)------------------------------
% 0.95/0.64  % (22431)------------------------------
% 1.13/0.65  % (22423)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.13/0.65  % (22443)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.13/0.65  % (22445)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 1.13/0.65  % (22443)Refutation found. Thanks to Tanya!
% 1.13/0.65  % SZS status Theorem for theBenchmark
% 1.13/0.65  % SZS output start Proof for theBenchmark
% 1.13/0.65  fof(f95,plain,(
% 1.13/0.65    $false),
% 1.13/0.65    inference(subsumption_resolution,[],[f94,f45])).
% 1.13/0.65  fof(f45,plain,(
% 1.13/0.65    l1_struct_0(sK0)),
% 1.13/0.65    inference(cnf_transformation,[],[f36])).
% 1.13/0.65  fof(f36,plain,(
% 1.13/0.65    (~r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 1.13/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f35,f34])).
% 1.13/0.65  fof(f34,plain,(
% 1.13/0.65    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 1.13/0.65    introduced(choice_axiom,[])).
% 1.13/0.65  fof(f35,plain,(
% 1.13/0.65    ? [X1] : (~r1_waybel_0(sK0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),u1_waybel_0(sK0,X1))) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.13/0.65    introduced(choice_axiom,[])).
% 1.13/0.65  fof(f17,plain,(
% 1.13/0.65    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 1.13/0.65    inference(flattening,[],[f16])).
% 1.13/0.65  fof(f16,plain,(
% 1.13/0.65    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 1.13/0.65    inference(ennf_transformation,[],[f11])).
% 1.13/0.65  fof(f11,negated_conjecture,(
% 1.13/0.65    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 1.13/0.65    inference(negated_conjecture,[],[f10])).
% 1.13/0.65  fof(f10,conjecture,(
% 1.13/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 1.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).
% 1.13/0.65  fof(f94,plain,(
% 1.13/0.65    ~l1_struct_0(sK0)),
% 1.13/0.65    inference(resolution,[],[f93,f47])).
% 1.13/0.65  fof(f47,plain,(
% 1.13/0.65    l1_waybel_0(sK1,sK0)),
% 1.13/0.65    inference(cnf_transformation,[],[f36])).
% 1.13/0.65  fof(f93,plain,(
% 1.13/0.65    ( ! [X0] : (~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0)) )),
% 1.13/0.65    inference(resolution,[],[f92,f65])).
% 1.13/0.65  fof(f65,plain,(
% 1.13/0.65    ( ! [X0,X1] : (l1_struct_0(X0) | ~l1_struct_0(X1) | ~l1_waybel_0(X0,X1)) )),
% 1.13/0.65    inference(resolution,[],[f51,f50])).
% 1.13/0.65  fof(f50,plain,(
% 1.13/0.65    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.13/0.65    inference(cnf_transformation,[],[f20])).
% 1.13/0.65  fof(f20,plain,(
% 1.13/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.13/0.65    inference(ennf_transformation,[],[f3])).
% 1.13/0.65  fof(f3,axiom,(
% 1.13/0.65    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.13/0.65  fof(f51,plain,(
% 1.13/0.65    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.13/0.65    inference(cnf_transformation,[],[f21])).
% 1.13/0.65  fof(f21,plain,(
% 1.13/0.65    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 1.13/0.65    inference(ennf_transformation,[],[f6])).
% 1.13/0.65  fof(f6,axiom,(
% 1.13/0.65    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 1.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 1.13/0.65  fof(f92,plain,(
% 1.13/0.65    ~l1_struct_0(sK1)),
% 1.13/0.65    inference(subsumption_resolution,[],[f91,f46])).
% 1.13/0.65  fof(f46,plain,(
% 1.13/0.65    ~v2_struct_0(sK1)),
% 1.13/0.65    inference(cnf_transformation,[],[f36])).
% 1.13/0.65  fof(f91,plain,(
% 1.13/0.65    ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.13/0.65    inference(resolution,[],[f90,f59])).
% 1.13/0.65  fof(f59,plain,(
% 1.13/0.65    ( ! [X0] : (l1_waybel_0(sK4(X0),X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.65    inference(cnf_transformation,[],[f43])).
% 1.13/0.65  fof(f43,plain,(
% 1.13/0.65    ! [X0] : ((~v2_struct_0(sK4(X0)) & l1_waybel_0(sK4(X0),X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f42])).
% 1.13/0.65  fof(f42,plain,(
% 1.13/0.65    ! [X0] : (? [X1] : (~v2_struct_0(X1) & l1_waybel_0(X1,X0)) => (~v2_struct_0(sK4(X0)) & l1_waybel_0(sK4(X0),X0)))),
% 1.13/0.65    introduced(choice_axiom,[])).
% 1.13/0.65  fof(f29,plain,(
% 1.13/0.65    ! [X0] : (? [X1] : (~v2_struct_0(X1) & l1_waybel_0(X1,X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.65    inference(flattening,[],[f28])).
% 1.13/0.65  fof(f28,plain,(
% 1.13/0.65    ! [X0] : (? [X1] : (~v2_struct_0(X1) & l1_waybel_0(X1,X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.65    inference(ennf_transformation,[],[f15])).
% 1.13/0.65  fof(f15,plain,(
% 1.13/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 1.13/0.65    inference(pure_predicate_removal,[],[f14])).
% 1.13/0.65  fof(f14,plain,(
% 1.13/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 1.13/0.65    inference(pure_predicate_removal,[],[f13])).
% 1.13/0.65  fof(f13,plain,(
% 1.13/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (v6_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 1.13/0.65    inference(pure_predicate_removal,[],[f12])).
% 1.13/0.65  fof(f12,plain,(
% 1.13/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (v7_waybel_0(X1) & v6_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 1.13/0.65    inference(pure_predicate_removal,[],[f9])).
% 1.13/0.65  fof(f9,axiom,(
% 1.13/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_yellow_6(X1,X0) & v7_waybel_0(X1) & v6_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 1.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_yellow_6)).
% 1.13/0.65  fof(f90,plain,(
% 1.13/0.65    ( ! [X0] : (~l1_waybel_0(X0,sK1)) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f89,f45])).
% 1.13/0.65  fof(f89,plain,(
% 1.13/0.65    ( ! [X0] : (~l1_struct_0(sK0) | ~l1_waybel_0(X0,sK1)) )),
% 1.13/0.65    inference(resolution,[],[f88,f47])).
% 1.13/0.65  fof(f88,plain,(
% 1.13/0.65    ( ! [X0,X1] : (~l1_waybel_0(sK1,X1) | ~l1_struct_0(X1) | ~l1_waybel_0(X0,sK1)) )),
% 1.13/0.65    inference(resolution,[],[f86,f65])).
% 1.13/0.65  fof(f86,plain,(
% 1.13/0.65    ( ! [X0] : (~l1_struct_0(sK1) | ~l1_waybel_0(X0,sK1)) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f83,f46])).
% 1.13/0.65  fof(f83,plain,(
% 1.13/0.65    ( ! [X0] : (~l1_waybel_0(X0,sK1) | ~l1_struct_0(sK1) | v2_struct_0(sK1)) )),
% 1.13/0.65    inference(resolution,[],[f82,f61])).
% 1.13/0.65  fof(f61,plain,(
% 1.13/0.65    ( ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.65    inference(cnf_transformation,[],[f31])).
% 1.13/0.65  fof(f31,plain,(
% 1.13/0.65    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.65    inference(flattening,[],[f30])).
% 1.13/0.65  fof(f30,plain,(
% 1.13/0.65    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.65    inference(ennf_transformation,[],[f8])).
% 1.13/0.65  fof(f8,axiom,(
% 1.13/0.65    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)))),
% 1.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).
% 1.13/0.65  fof(f82,plain,(
% 1.13/0.65    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f81,f47])).
% 1.13/0.65  fof(f81,plain,(
% 1.13/0.65    ( ! [X0] : (~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f80,f44])).
% 1.13/0.65  fof(f44,plain,(
% 1.13/0.65    ~v2_struct_0(sK0)),
% 1.13/0.65    inference(cnf_transformation,[],[f36])).
% 1.13/0.65  fof(f80,plain,(
% 1.13/0.65    ( ! [X0] : (v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f79,f45])).
% 1.13/0.65  fof(f79,plain,(
% 1.13/0.65    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f78,f46])).
% 1.13/0.65  fof(f78,plain,(
% 1.13/0.65    ( ! [X0] : (v2_struct_0(sK1) | ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 1.13/0.65    inference(resolution,[],[f77,f48])).
% 1.13/0.65  fof(f48,plain,(
% 1.13/0.65    ~r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 1.13/0.65    inference(cnf_transformation,[],[f36])).
% 1.13/0.65  fof(f77,plain,(
% 1.13/0.65    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f76,f56])).
% 1.13/0.65  fof(f56,plain,(
% 1.13/0.65    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1)) | r1_waybel_0(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.65    inference(cnf_transformation,[],[f41])).
% 1.13/0.65  fof(f41,plain,(
% 1.13/0.65    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3)) & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f40,f39])).
% 1.13/0.65  fof(f39,plain,(
% 1.13/0.65    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2) & r1_orders_2(X1,X3,sK2(X0,X1,X2,X3)) & m1_subset_1(sK2(X0,X1,X2,X3),u1_struct_0(X1))))),
% 1.13/0.65    introduced(choice_axiom,[])).
% 1.13/0.65  fof(f40,plain,(
% 1.13/0.65    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,sK3(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))))),
% 1.13/0.65    introduced(choice_axiom,[])).
% 1.13/0.65  fof(f38,plain,(
% 1.13/0.65    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.65    inference(rectify,[],[f37])).
% 1.13/0.65  fof(f37,plain,(
% 1.13/0.65    ! [X0] : (! [X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.65    inference(nnf_transformation,[],[f27])).
% 1.13/0.65  fof(f27,plain,(
% 1.13/0.65    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.65    inference(flattening,[],[f26])).
% 1.13/0.65  fof(f26,plain,(
% 1.13/0.65    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.65    inference(ennf_transformation,[],[f4])).
% 1.13/0.65  fof(f4,axiom,(
% 1.13/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 1.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).
% 1.13/0.65  fof(f76,plain,(
% 1.13/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 1.13/0.65    inference(duplicate_literal_removal,[],[f75])).
% 1.13/0.65  fof(f75,plain,(
% 1.13/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)),X2),u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0) | r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.65    inference(resolution,[],[f74,f58])).
% 1.13/0.65  fof(f58,plain,(
% 1.13/0.65    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_waybel_0(X0,X1,sK2(X0,X1,X2,X3)),X2) | r1_waybel_0(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.65    inference(cnf_transformation,[],[f41])).
% 1.13/0.65  fof(f74,plain,(
% 1.13/0.65    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X2,X1,X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_waybel_0(X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X2) | v2_struct_0(X2)) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f73,f65])).
% 1.13/0.65  fof(f73,plain,(
% 1.13/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X2,X1,X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1))) | ~l1_waybel_0(X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X2) | v2_struct_0(X2) | ~l1_struct_0(X1)) )),
% 1.13/0.65    inference(duplicate_literal_removal,[],[f72])).
% 1.13/0.65  fof(f72,plain,(
% 1.13/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(X2,X1,X0),k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),u1_waybel_0(X2,X1))) | ~l1_waybel_0(X1,X2) | v2_struct_0(X1) | ~l1_struct_0(X2) | v2_struct_0(X2) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.13/0.65    inference(resolution,[],[f71,f52])).
% 1.13/0.65  fof(f52,plain,(
% 1.13/0.65    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.65    inference(cnf_transformation,[],[f23])).
% 1.13/0.65  fof(f23,plain,(
% 1.13/0.65    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.65    inference(flattening,[],[f22])).
% 1.13/0.65  fof(f22,plain,(
% 1.13/0.65    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.65    inference(ennf_transformation,[],[f2])).
% 1.13/0.65  fof(f2,axiom,(
% 1.13/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.13/0.65  fof(f71,plain,(
% 1.13/0.65    ( ! [X2,X0,X1] : (v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f70,f52])).
% 1.13/0.65  fof(f70,plain,(
% 1.13/0.65    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f69,f62])).
% 1.13/0.65  fof(f62,plain,(
% 1.13/0.65    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.13/0.65    inference(cnf_transformation,[],[f33])).
% 1.13/0.65  fof(f33,plain,(
% 1.13/0.65    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 1.13/0.65    inference(flattening,[],[f32])).
% 1.13/0.65  fof(f32,plain,(
% 1.13/0.65    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 1.13/0.65    inference(ennf_transformation,[],[f7])).
% 1.13/0.65  fof(f7,axiom,(
% 1.13/0.65    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 1.13/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 1.13/0.65  fof(f69,plain,(
% 1.13/0.65    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~v1_funct_1(u1_waybel_0(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.13/0.65    inference(subsumption_resolution,[],[f68,f63])).
% 1.13/0.65  fof(f63,plain,(
% 1.13/0.65    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.13/0.65    inference(cnf_transformation,[],[f33])).
% 1.13/0.65  % (22426)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 1.13/0.65  % (22426)Refutation not found, incomplete strategy% (22426)------------------------------
% 1.13/0.65  % (22426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.65  % (22426)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.65  
% 1.13/0.65  % (22426)Memory used [KB]: 10618
% 1.13/0.65  % (22426)Time elapsed: 0.072 s
% 1.13/0.65  % (22426)------------------------------
% 1.13/0.65  % (22426)------------------------------
% 1.13/0.66  % (22424)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.13/0.66  % (22425)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 1.13/0.67  % (22440)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.13/0.67  % (22440)Refutation not found, incomplete strategy% (22440)------------------------------
% 1.13/0.67  % (22440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.67  % (22440)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.67  
% 1.13/0.67  % (22440)Memory used [KB]: 1535
% 1.13/0.67  % (22440)Time elapsed: 0.001 s
% 1.13/0.67  % (22440)------------------------------
% 1.13/0.67  % (22440)------------------------------
% 1.13/0.67  % (22444)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.13/0.67  % (22432)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.13/0.67  fof(f68,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(u1_waybel_0(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.13/0.67    inference(subsumption_resolution,[],[f67,f64])).
% 1.13/0.67  fof(f64,plain,(
% 1.13/0.67    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f33])).
% 1.13/0.67  fof(f67,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(u1_waybel_0(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.13/0.67    inference(duplicate_literal_removal,[],[f66])).
% 1.13/0.67  fof(f66,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (r2_hidden(k2_waybel_0(X1,X0,X2),k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0))) | ~m1_subset_1(u1_waybel_0(X1,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(u1_waybel_0(X1,X0),u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(u1_waybel_0(X1,X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 1.13/0.67    inference(superposition,[],[f49,f53])).
% 1.13/0.67  fof(f53,plain,(
% 1.13/0.67    ( ! [X2,X0,X1] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f25])).
% 1.13/0.67  fof(f25,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.13/0.67    inference(flattening,[],[f24])).
% 1.13/0.67  fof(f24,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.13/0.67    inference(ennf_transformation,[],[f5])).
% 1.13/0.67  fof(f5,axiom,(
% 1.13/0.67    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2))))),
% 1.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).
% 1.13/0.67  fof(f49,plain,(
% 1.13/0.67    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.13/0.67    inference(cnf_transformation,[],[f19])).
% 1.13/0.67  fof(f19,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.13/0.67    inference(flattening,[],[f18])).
% 1.13/0.67  fof(f18,plain,(
% 1.13/0.67    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.13/0.67    inference(ennf_transformation,[],[f1])).
% 1.13/0.67  fof(f1,axiom,(
% 1.13/0.67    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 1.13/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
% 1.13/0.67  % SZS output end Proof for theBenchmark
% 1.13/0.67  % (22443)------------------------------
% 1.13/0.67  % (22443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.67  % (22443)Termination reason: Refutation
% 1.13/0.67  
% 1.13/0.67  % (22443)Memory used [KB]: 6140
% 1.13/0.67  % (22443)Time elapsed: 0.083 s
% 1.13/0.67  % (22443)------------------------------
% 1.13/0.67  % (22443)------------------------------
% 1.13/0.67  % (22439)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.13/0.67  % (22277)Success in time 0.311 s
%------------------------------------------------------------------------------
