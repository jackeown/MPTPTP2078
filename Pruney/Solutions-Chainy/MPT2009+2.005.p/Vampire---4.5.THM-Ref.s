%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 546 expanded)
%              Number of leaves         :   17 ( 186 expanded)
%              Depth                    :   13
%              Number of atoms          :  295 (2565 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(subsumption_resolution,[],[f354,f218])).

fof(f218,plain,(
    ~ r2_hidden(k2_waybel_0(sK2,sK3,sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3)))),k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f119,f165,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(k2_waybel_0(X2,X1,sK4(X0,X1,X2,X3)),X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_hidden(k2_waybel_0(X2,X1,sK4(X0,X1,X2,X3)),X0)
              & r1_orders_2(X1,X3,sK4(X0,X1,X2,X3))
              & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1)) )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
              | ~ r1_orders_2(X1,sK5(X0,X1,X2),X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f39,f38])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X2,X1,sK4(X0,X1,X2,X3)),X0)
        & r1_orders_2(X1,X3,sK4(X0,X1,X2,X3))
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
            | ~ r1_orders_2(X1,sK5(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_hidden(k2_waybel_0(X2,X1,X4),X0)
                & r1_orders_2(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_hidden(k2_waybel_0(X2,X1,X6),X0)
                | ~ r1_orders_2(X1,X5,X6)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
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
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f165,plain,(
    m1_subset_1(k4_yellow_6(sK3,sK6(sK3)),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f45,f103,f109,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(f109,plain,(
    l1_waybel_0(sK6(sK3),sK3) ),
    inference(unit_resulting_resolution,[],[f103,f62])).

fof(f62,plain,(
    ! [X0] :
      ( l1_waybel_0(sK6(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_waybel_0(sK6(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
     => l1_waybel_0(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_waybel_0)).

fof(f103,plain,(
    l1_struct_0(sK3) ),
    inference(unit_resulting_resolution,[],[f93,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f93,plain,(
    l1_orders_2(sK3) ),
    inference(unit_resulting_resolution,[],[f44,f46,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f46,plain,(
    l1_waybel_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_waybel_0(sK2,sK3,k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)))
    & l1_waybel_0(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK2,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),u1_waybel_0(sK2,X1)))
          & l1_waybel_0(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK2,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),u1_waybel_0(sK2,X1)))
        & l1_waybel_0(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK2,sK3,k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)))
      & l1_waybel_0(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f44,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f119,plain,(
    ~ sP0(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f47,f89,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_waybel_0(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_waybel_0(X0,X1,X2)
            | ~ sP0(X2,X1,X0) )
          & ( sP0(X2,X1,X0)
            | ~ r1_waybel_0(X0,X1,X2) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_waybel_0(X0,X1,X2)
        <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f89,plain,(
    sP1(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f30,f29])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f47,plain,(
    ~ r1_waybel_0(sK2,sK3,k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f354,plain,(
    r2_hidden(k2_waybel_0(sK2,sK3,sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3)))),k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3))) ),
    inference(backward_demodulation,[],[f265,f261])).

fof(f261,plain,(
    k2_waybel_0(sK2,sK3,sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3)))) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3),sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3)))) ),
    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f216,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f216,plain,(
    m1_subset_1(sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3))),u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f119,f165,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f265,plain,(
    r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3),sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3)))),k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f108,f72,f90,f91,f92,f216,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f92,plain,(
    m1_subset_1(u1_waybel_0(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2)))) ),
    inference(unit_resulting_resolution,[],[f44,f46,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f91,plain,(
    v1_funct_2(u1_waybel_0(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f44,f46,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,(
    v1_funct_1(u1_waybel_0(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f44,f46,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f43,f44,f61])).

fof(f61,plain,(
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

fof(f108,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(unit_resulting_resolution,[],[f45,f103,f61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:19:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (18003)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (18011)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (18011)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f356,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f354,f218])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ~r2_hidden(k2_waybel_0(sK2,sK3,sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3)))),k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f119,f165,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | ~r2_hidden(k2_waybel_0(X2,X1,sK4(X0,X1,X2,X3)),X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_hidden(k2_waybel_0(X2,X1,sK4(X0,X1,X2,X3)),X0) & r1_orders_2(X1,X3,sK4(X0,X1,X2,X3)) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) | ~r1_orders_2(X1,sK5(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f39,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X3,X2,X1,X0] : (? [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_hidden(k2_waybel_0(X2,X1,sK4(X0,X1,X2,X3)),X0) & r1_orders_2(X1,X3,sK4(X0,X1,X2,X3)) & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) | ~r1_orders_2(X1,sK5(X0,X1,X2),X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X2,X1,X4),X0) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_hidden(k2_waybel_0(X2,X1,X6),X0) | ~r1_orders_2(X1,X5,X6) | ~m1_subset_1(X6,u1_struct_0(X1))) & m1_subset_1(X5,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ! [X3] : (? [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X2,X1,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    m1_subset_1(k4_yellow_6(sK3,sK6(sK3)),u1_struct_0(sK3))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f45,f103,f109,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    l1_waybel_0(sK6(sK3),sK3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f103,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0] : (l1_waybel_0(sK6(X0),X0) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0] : (l1_waybel_0(sK6(X0),X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : l1_waybel_0(X1,X0) => l1_waybel_0(sK6(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => ? [X1] : l1_waybel_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_waybel_0)).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    l1_struct_0(sK3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f93,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    l1_orders_2(sK3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f44,f46,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    l1_waybel_0(sK3,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    (~r1_waybel_0(sK2,sK3,k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3))) & l1_waybel_0(sK3,sK2) & ~v2_struct_0(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f13,f33,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK2,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),u1_waybel_0(sK2,X1))) & l1_waybel_0(X1,sK2) & ~v2_struct_0(X1)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X1] : (~r1_waybel_0(sK2,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),u1_waybel_0(sK2,X1))) & l1_waybel_0(X1,sK2) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK2,sK3,k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3))) & l1_waybel_0(sK3,sK2) & ~v2_struct_0(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    l1_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ~v2_struct_0(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ~sP0(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f47,f89,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_waybel_0(X0,X1,X2) | ~sP0(X2,X1,X0) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : ((r1_waybel_0(X0,X1,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r1_waybel_0(X0,X1,X2))) | ~sP1(X0,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> sP0(X2,X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    sP1(sK2,sK3)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP1(X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (sP1(X0,X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(definition_folding,[],[f15,f30,f29])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ~v2_struct_0(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ~r1_waybel_0(sK2,sK3,k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)))),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f354,plain,(
% 0.21/0.53    r2_hidden(k2_waybel_0(sK2,sK3,sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3)))),k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)))),
% 0.21/0.53    inference(backward_demodulation,[],[f265,f261])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    k2_waybel_0(sK2,sK3,sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3)))) = k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3),sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3))))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f43,f44,f45,f46,f216,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    m1_subset_1(sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3))),u1_struct_0(sK3))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f119,f165,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    r2_hidden(k3_funct_2(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3),sK4(k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)),sK3,sK2,k4_yellow_6(sK3,sK6(sK3)))),k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),u1_waybel_0(sK2,sK3)))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f108,f72,f90,f91,f92,f216,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    m1_subset_1(u1_waybel_0(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK2))))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f44,f46,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    v1_funct_2(u1_waybel_0(sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f44,f46,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    v1_funct_1(u1_waybel_0(sK2,sK3))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f44,f46,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f43,f44,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f45,f103,f61])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (18011)------------------------------
% 0.21/0.53  % (18011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (18011)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (18011)Memory used [KB]: 1918
% 0.21/0.53  % (18011)Time elapsed: 0.078 s
% 0.21/0.53  % (18011)------------------------------
% 0.21/0.53  % (18011)------------------------------
% 0.21/0.54  % (17993)Success in time 0.166 s
%------------------------------------------------------------------------------
