%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1915+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:37 EST 2020

% Result     : Theorem 3.98s
% Output     : Refutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 153 expanded)
%              Number of leaves         :    8 (  61 expanded)
%              Depth                    :    8
%              Number of atoms          :  169 ( 807 expanded)
%              Number of equality atoms :   39 ( 182 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11501,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6522,f6649])).

fof(f6649,plain,(
    ! [X0] : g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) != g1_orders_2(u1_struct_0(k3_yellow_6(sK8,sK9,sK10)),X0) ),
    inference(unit_resulting_resolution,[],[f4759,f5607,f4875])).

fof(f4875,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f3973])).

fof(f3973,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f1926])).

fof(f1926,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f5607,plain,(
    m1_subset_1(u1_orders_2(sK8),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)))) ),
    inference(unit_resulting_resolution,[],[f4755,f4905])).

fof(f4905,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4003])).

fof(f4003,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1905])).

fof(f1905,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f4755,plain,(
    l1_orders_2(sK8) ),
    inference(cnf_transformation,[],[f4414])).

fof(f4414,plain,
    ( u1_struct_0(sK8) != u1_struct_0(k3_yellow_6(sK8,sK9,sK10))
    & m1_subset_1(sK10,u1_struct_0(sK9))
    & l1_struct_0(sK9)
    & ~ v2_struct_0(sK9)
    & l1_orders_2(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f3871,f4413,f4412,f4411])).

fof(f4411,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(sK8) != u1_struct_0(k3_yellow_6(sK8,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f4412,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( u1_struct_0(sK8) != u1_struct_0(k3_yellow_6(sK8,X1,X2))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( u1_struct_0(sK8) != u1_struct_0(k3_yellow_6(sK8,sK9,X2))
          & m1_subset_1(X2,u1_struct_0(sK9)) )
      & l1_struct_0(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f4413,plain,
    ( ? [X2] :
        ( u1_struct_0(sK8) != u1_struct_0(k3_yellow_6(sK8,sK9,X2))
        & m1_subset_1(X2,u1_struct_0(sK9)) )
   => ( u1_struct_0(sK8) != u1_struct_0(k3_yellow_6(sK8,sK9,sK10))
      & m1_subset_1(sK10,u1_struct_0(sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f3871,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f3870])).

fof(f3870,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( u1_struct_0(X0) != u1_struct_0(k3_yellow_6(X0,X1,X2))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3853])).

fof(f3853,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f3852])).

fof(f3852,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => u1_struct_0(X0) = u1_struct_0(k3_yellow_6(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_6)).

fof(f4759,plain,(
    u1_struct_0(sK8) != u1_struct_0(k3_yellow_6(sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f4414])).

fof(f6522,plain,(
    g1_orders_2(u1_struct_0(sK8),u1_orders_2(sK8)) = g1_orders_2(u1_struct_0(k3_yellow_6(sK8,sK9,sK10)),u1_orders_2(k3_yellow_6(sK8,sK9,sK10))) ),
    inference(unit_resulting_resolution,[],[f4755,f4756,f4757,f4758,f5641,f5644,f5553])).

fof(f5553,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(k3_yellow_6(X0,X1,X2)),u1_orders_2(k3_yellow_6(X0,X1,X2)))
      | ~ l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f4764])).

fof(f4764,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3))
      | k3_yellow_6(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X1)
      | ~ v6_waybel_0(X3,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f4416])).

fof(f4416,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f4415])).

fof(f4415,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_yellow_6(X0,X1,X2) = X3
                      | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                    & ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                        & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) )
                      | k3_yellow_6(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f3877])).

fof(f3877,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3876])).

fof(f3876,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) )
                  | ~ l1_waybel_0(X3,X1)
                  | ~ v6_waybel_0(X3,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3802])).

fof(f3802,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X1)
                    & v6_waybel_0(X3,X1) )
                 => ( k3_yellow_6(X0,X1,X2) = X3
                  <=> ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),u1_waybel_0(X1,X3),k8_funcop_1(u1_struct_0(X1),u1_struct_0(X3),X2))
                      & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_yellow_6)).

fof(f5644,plain,(
    l1_waybel_0(k3_yellow_6(sK8,sK9,sK10),sK9) ),
    inference(unit_resulting_resolution,[],[f4755,f4756,f4757,f4758,f4761])).

fof(f4761,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3873])).

fof(f3873,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f3872])).

fof(f3872,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3807])).

fof(f3807,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0) )
     => ( l1_waybel_0(k3_yellow_6(X0,X1,X2),X1)
        & v6_waybel_0(k3_yellow_6(X0,X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_6)).

fof(f5641,plain,(
    v6_waybel_0(k3_yellow_6(sK8,sK9,sK10),sK9) ),
    inference(unit_resulting_resolution,[],[f4755,f4756,f4757,f4758,f4760])).

fof(f4760,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k3_yellow_6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f3873])).

fof(f4758,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f4414])).

fof(f4757,plain,(
    l1_struct_0(sK9) ),
    inference(cnf_transformation,[],[f4414])).

fof(f4756,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f4414])).
%------------------------------------------------------------------------------
